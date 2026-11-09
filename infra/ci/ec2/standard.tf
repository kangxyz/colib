module "standard_runners" {
  count   = var.standard_enabled ? 1 : 0
  source  = "github-aws-runners/github-runner/aws"
  version = "8.0.0"

  aws_region = var.aws_region
  prefix     = "${var.prefix}-standard"
  vpc_id     = aws_vpc.runner.id
  subnet_ids = [aws_subnet.runner.id]

  github_app = local.github_app

  enable_organization_runners             = false
  repository_white_list                   = ["kangxyz/colib"]
  runner_extra_labels                     = ["colib-standard-ec2"]
  runner_disable_default_labels           = true
  enable_runner_bidirectional_label_match = true
  eventbridge                             = { enable = false }

  enable_ephemeral_runners                = false
  enable_jit_config                       = false
  runner_hook_job_started                 = file("${path.module}/warmup-runner-hook.sh")
  enable_job_queued_check                 = true
  runners_maximum_count                   = 1
  scale_up_reserved_concurrent_executions = 1
  idle_config                             = []
  pool_config                             = []
  instance_target_capacity_type           = "on-demand"
  instance_types                          = ["m7i.xlarge"]
  runner_architecture                     = "x64"
  runner_run_as                           = "ubuntu"
  runner_as_root                          = false
  associate_public_ipv4_address           = true
  minimum_running_time_in_minutes         = 10
  runner_boot_time_in_minutes             = 15
  scale_down_schedule_expression          = "cron(* * * * ? *)"
  scale_down_idle_confirmation_seconds    = 900
  job_retry                               = { enable = false }

  ami                     = local.ubuntu_ami
  userdata_template       = "${path.module}/ubuntu-user-data.sh.tftpl"
  userdata_pre_install    = local.expiry_script
  block_device_mappings   = local.runner_disk
  runner_metadata_options = local.runner_metadata

  webhook_lambda_zip                = "${path.module}/lambdas/warmup-webhook.zip"
  runner_binaries_syncer_lambda_zip = "${path.module}/lambdas/runner-binaries-syncer.zip"
  runners_lambda_zip                = "${path.module}/lambdas/runners.zip"

  enable_cloudwatch_agent               = true
  enable_user_data_debug_logging_runner = false
  logging_retention_in_days             = 7
  log_level                             = "info"

  depends_on = [aws_route_table_association.runner]
}
