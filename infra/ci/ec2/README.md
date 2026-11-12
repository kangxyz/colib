# Colib EC2 CI

Colib uses on-demand EC2 runners for owner pushes and manual runs on repository
branches. Both `COLIB_SELF_HOSTED_ENABLED` and `COLIB_PARALLEL_RUNNER_ENABLED`
must be `true` to route new CI runs to EC2. Pull requests and the manual
`hosted` profile use GitHub-hosted runners. See [Lean CI](../../../.github/LEAN_CI.md)
for the job flow and cache handling.

## Runner lifecycle

The controller polls GitHub every minute for queued Build jobs in
`.github/workflows/ci.yml`. It checks the event, repository, actors and job
label before claiming an EC2 lease. Each attempt receives a runner with the
`colib-ci-run-<run>-<attempt>` label. Build and Test share its checkout and
native store and verify the identity at handoff. A completed run releases the
instance and its runner registration. If the assigned instance disappears,
cancel the attempt and rerun all jobs so Build and Test share a new host.

The production limit is three concurrent attempts across branches. Additional
runs wait in the GitHub queue. Each `m7i.4xlarge` instance has 16 vCPUs, 64 GiB of
RAM and a 200 GiB encrypted gp3 disk deleted on termination. The runner subnet
has no NAT gateway and the security group has no inbound rules. IMDSv2 is
required. The 360-minute instance watchdog also runs if the controller becomes
unavailable. Build and Test renew the watchdog and have job limits of 240 and
90 minutes respectively.

The runner distribution and instance role come from the pinned
[GitHub runner module v8.0.0](https://github.com/github-aws-runners/terraform-aws-github-runner/tree/v8.0.0).
The scheduled controller has its own IAM role and uses a separate launch
template, security group and DynamoDB lease table.

## Deployment

Use Terraform 1.13.5 and the committed provider lock. Authenticate with AWS in
`us-east-1`. The encrypted, versioned state bucket is
`colib-ec2-terraform-975049960217` and the state key is `runner/terraform.tfstate`.
Enable S3 lockfiles with `use_lockfile = true` in the backend configuration.
An AWS CLI login profile can supply Terraform credentials through a local
`credential_process` running `aws configure export-credentials --format process`.
Keep local credentials, variables, plans and Lambda archives outside Git. The
AWS provider verifies that the authenticated account matches `aws_account_id`.

The GitHub App installation must include `kangxyz/colib` and grant repository
Administration write and Actions read. Reference the existing base64-encoded
App key in SSM with `github_app_key_ssm_name`. The upstream module also references
the existing webhook secret at `/colib-ec2/app/webhook-secret`.

Use `enabled=true`, `guarded_ci=true` and `parallel_runner_limit=3` in the
production variables file. Build the Lambda archives and inspect the plan
before applying it.

```bash
bash fetch-lambdas.sh
terraform init -backend-config=/path/to/private/state.backend.hcl
terraform validate
terraform plan -var-file=/path/to/private/deployment.tfvars.json -out=colib.tfplan
terraform show colib.tfplan
terraform apply colib.tfplan
```

Verify the runner distribution in S3 and the schedule
`colib-ec2-parallel-reconcile` after deployment. An owner dispatch with the
`ec2` profile exercises Build and Test on the same instance and checks that the
controller releases it afterward. To pause new EC2 runs, set
`COLIB_SELF_HOSTED_ENABLED=false` and allow existing attempts to finish.

## Retired webhooks

The two repository `workflow_job` hooks and the corresponding AWS API Gateway
default endpoints are disabled. The scheduled controller reads GitHub's Actions
API directly.

The pinned runner module still declares the old gateways. A full Terraform
apply can re-enable their default endpoints. After applying a plan that touches
either API, check both endpoints. The Terraform outputs `webhook_url` and
`standard_webhook_url` identify the APIs when those resources exist. Use the
deployment's AWS account and region to restore the disabled setting.

```bash
aws apigatewayv2 update-api --api-id API_ID --disable-execute-api-endpoint
aws apigatewayv2 get-api --api-id API_ID --query DisableExecuteApiEndpoint
```
