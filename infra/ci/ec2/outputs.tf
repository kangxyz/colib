output "webhook_url" {
  value = module.runners.webhook.endpoint
}

output "runner_launch_template_id" {
  value = module.runners.runners.launch_template_id
}

output "region" {
  value = var.aws_region
}

output "github_runner_labels" {
  value = local.guarded_runner ? ["colib-dependency-warmup"] : ["self-hosted", "linux", "x64", "colib-ec2"]
}


output "standard_webhook_url" {
  value = var.standard_enabled ? module.standard_runners[0].webhook.endpoint : null
}
