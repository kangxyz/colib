locals {
  parallel_count      = var.parallel_runner_limit > 0 ? 1 : 0
  parallel_name       = "${var.prefix}-parallel"
  parallel_token_path = "/github-action-runners/${var.prefix}/runners/tokens"
  parallel_ec2_arn    = "arn:aws:ec2:${var.aws_region}:${var.aws_account_id}"
  parallel_archive    = "${path.module}/lambdas/parallel-controller.zip"
}

resource "aws_security_group" "parallel" {
  count       = local.parallel_count
  name_prefix = "${local.parallel_name}-"
  description = "Outbound connections for Colib CI runners"
  vpc_id      = aws_vpc.runner.id

  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

resource "aws_launch_template" "parallel" {
  count                                = local.parallel_count
  name_prefix                          = "${local.parallel_name}-"
  image_id                             = module.runners.runners.launch_template_ami_id
  instance_type                        = var.instance_type
  instance_initiated_shutdown_behavior = "terminate"

  iam_instance_profile {
    name = "${var.prefix}-runner-profile"
  }

  network_interfaces {
    device_index                = 0
    subnet_id                   = aws_subnet.runner.id
    security_groups             = [aws_security_group.parallel[0].id]
    associate_public_ip_address = true
    delete_on_termination       = true
  }

  metadata_options {
    http_endpoint               = "enabled"
    http_tokens                 = "required"
    http_put_response_hop_limit = 1
    instance_metadata_tags      = "enabled"
  }

  block_device_mappings {
    device_name = local.runner_disk[0].device_name
    ebs {
      volume_size           = local.runner_disk[0].volume_size
      volume_type           = local.runner_disk[0].volume_type
      encrypted             = true
      delete_on_termination = true
    }
  }

  user_data = base64gzip(templatefile("${path.module}/ubuntu-user-data.sh.tftpl", {
    pre_install      = local.expiry_script
    install_runner   = <<-SHELL
      parallel_token_path="${local.parallel_token_path}"
      mkdir -p /opt/actions-runner
      aws s3 cp --region "${var.aws_region}" "${module.runners.binaries_syncer.location}" /tmp/colib-runner.tar.gz
      tar -xzf /tmp/colib-runner.tar.gz -C /opt/actions-runner
      rm -f /tmp/colib-runner.tar.gz
    SHELL
    post_install     = ""
    hook_job_started = file("${path.module}/parallel-hook.sh")
    start_runner     = file("${path.module}/parallel-start.sh")
  }))

  lifecycle {
    precondition {
      condition     = var.enabled && var.guarded_ci
      error_message = "The parallel runner uses the guarded Colib distribution and instance role."
    }
  }
}

resource "aws_dynamodb_table" "parallel_leases" {
  count        = local.parallel_count
  name         = "${local.parallel_name}-leases"
  billing_mode = "PAY_PER_REQUEST"
  hash_key     = "run_key"

  attribute {
    name = "run_key"
    type = "S"
  }

  ttl {
    attribute_name = "expires_at"
    enabled        = true
  }
}

resource "aws_iam_role" "parallel_controller" {
  count = local.parallel_count
  name  = "${local.parallel_name}-controller"
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Allow"
      Action    = "sts:AssumeRole"
      Principal = { Service = "lambda.amazonaws.com" }
    }]
  })
}

resource "aws_cloudwatch_log_group" "parallel_controller" {
  count             = local.parallel_count
  name              = "/aws/lambda/${local.parallel_name}-controller"
  retention_in_days = 7
}

resource "aws_iam_role_policy" "parallel_controller" {
  count = local.parallel_count
  role  = aws_iam_role.parallel_controller[0].name
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect   = "Allow"
        Action   = ["logs:CreateLogStream", "logs:PutLogEvents"]
        Resource = "${aws_cloudwatch_log_group.parallel_controller[0].arn}:*"
      },
      {
        Effect   = "Allow"
        Action   = ["dynamodb:Scan", "dynamodb:PutItem"]
        Resource = aws_dynamodb_table.parallel_leases[0].arn
      },
      {
        Effect   = "Allow"
        Action   = "ssm:GetParameter"
        Resource = local.github_app.key_base64_ssm.arn
      },
      {
        Effect   = "Allow"
        Action   = "ssm:GetParameters"
        Resource = trimprefix(module.runners.runners.launch_template_ami_id, "resolve:ssm:")
      },
      {
        Effect   = "Allow"
        Action   = ["ssm:PutParameter", "ssm:AddTagsToResource", "ssm:DeleteParameter"]
        Resource = "${local.parameter_arn_prefix}${local.parallel_token_path}/i-*"
      },
      {
        Effect   = "Allow"
        Action   = "ec2:DescribeInstances"
        Resource = "*"
      },
      {
        Effect = "Allow"
        Action = "ec2:RunInstances"
        Resource = [
          aws_launch_template.parallel[0].arn,
          "${local.parallel_ec2_arn}:subnet/${aws_subnet.runner.id}",
          aws_security_group.parallel[0].arn,
          "arn:aws:ec2:${var.aws_region}::image/*"
        ]
      },
      {
        Effect = "Allow"
        Action = "ec2:RunInstances"
        Resource = [
          "${local.parallel_ec2_arn}:instance/*",
          "${local.parallel_ec2_arn}:network-interface/*",
          "${local.parallel_ec2_arn}:volume/*"
        ]
        Condition = { ArnEquals = { "ec2:LaunchTemplate" = aws_launch_template.parallel[0].arn } }
      },
      {
        Effect   = "Allow"
        Action   = "ec2:CreateTags"
        Resource = "${local.parallel_ec2_arn}:instance/*"
        Condition = { StringEquals = {
          "ec2:CreateAction"               = "RunInstances"
          "aws:RequestTag/ghr:environment" = local.parallel_name
        } }
      },
      {
        Effect    = "Allow"
        Action    = "ec2:TerminateInstances"
        Resource  = "${local.parallel_ec2_arn}:instance/*"
        Condition = { StringEquals = { "ec2:ResourceTag/ghr:environment" = local.parallel_name } }
      },
      {
        Effect    = "Allow"
        Action    = "iam:PassRole"
        Resource  = one(module.runners.runners.role_runner).arn
        Condition = { StringEquals = { "iam:PassedToService" = "ec2.amazonaws.com" } }
      }
    ]
  })
}

resource "aws_lambda_function" "parallel_controller" {
  count                          = local.parallel_count
  function_name                  = "${local.parallel_name}-controller"
  role                           = aws_iam_role.parallel_controller[0].arn
  runtime                        = "nodejs22.x"
  handler                        = "parallel-controller.handler"
  filename                       = local.parallel_archive
  source_code_hash               = filebase64sha256(local.parallel_archive)
  reserved_concurrent_executions = 1
  memory_size                    = 256
  timeout                        = 50

  environment {
    variables = {
      GITHUB_APP_ID      = var.github_app_id
      GITHUB_KEY         = local.app_key_name
      LEASE_TABLE        = aws_dynamodb_table.parallel_leases[0].name
      RUNNER_ENVIRONMENT = local.parallel_name
      RUNNER_TOKEN_PATH  = local.parallel_token_path
      LAUNCH_TEMPLATE    = aws_launch_template.parallel[0].id
      TEMPLATE_VERSION   = tostring(aws_launch_template.parallel[0].latest_version)
      RUNNER_LIMIT       = tostring(var.parallel_runner_limit)
    }
  }

  depends_on = [aws_iam_role_policy.parallel_controller]
}

resource "aws_cloudwatch_event_rule" "parallel_controller" {
  count               = local.parallel_count
  name                = "${local.parallel_name}-reconcile"
  schedule_expression = "rate(1 minute)"
}

resource "aws_cloudwatch_event_target" "parallel_controller" {
  count = local.parallel_count
  rule  = aws_cloudwatch_event_rule.parallel_controller[0].name
  arn   = aws_lambda_function.parallel_controller[0].arn
  retry_policy {
    maximum_event_age_in_seconds = 60
    maximum_retry_attempts       = 0
  }
}

resource "aws_lambda_permission" "parallel_controller" {
  count         = local.parallel_count
  statement_id  = "AllowColibRunnerReconcile"
  action        = "lambda:InvokeFunction"
  function_name = aws_lambda_function.parallel_controller[0].function_name
  principal     = "events.amazonaws.com"
  source_arn    = aws_cloudwatch_event_rule.parallel_controller[0].arn
}
