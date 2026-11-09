set -euo pipefail

metadata=http://169.254.169.254/latest
imds_token=$(curl -fsS --retry 3 --connect-timeout 3 -X PUT \
  -H 'X-aws-ec2-metadata-token-ttl-seconds: 180' "$metadata/api/token")
read_metadata() {
  curl -fsS --retry 3 --connect-timeout 3 -H "X-aws-ec2-metadata-token: $imds_token" "$metadata/$1"
}

instance_id=$(read_metadata meta-data/instance-id)
lease=$(read_metadata meta-data/tags/instance/colib-ci-run)
region=$(read_metadata dynamic/instance-identity/document | jq -er .region)
[[ "$lease" =~ ^[1-9][0-9]*-[1-9][0-9]*$ ]]
label="colib-ci-run-$lease"
parameter="$parallel_token_path/$instance_id"
runner_token=
for attempt in {1..60}; do
  runner_token=$(aws ssm get-parameter --region "$region" --name "$parameter" \
    --with-decryption --query Parameter.Value --output text 2>/dev/null || true)
  if [[ -n "$runner_token" && "$runner_token" != None ]]; then break; fi
  sleep 5
done
[[ -n "$runner_token" && "$runner_token" != None ]]

cd /opt/actions-runner
chown -R ubuntu:ubuntu .
sudo -u ubuntu -- ./config.sh --unattended --no-default-labels --work _work \
  --url https://github.com/kangxyz/colib --token "$runner_token" \
  --name "$label-$instance_id" --labels "$label"
unset runner_token
aws ssm delete-parameter --region "$region" --name "$parameter" || true
install -o root -g root -m 0644 /dev/null /etc/colib-ci-runner-mode
printf '%s\n' colib-ci-runner-v1 > /etc/colib-ci-runner-mode
./svc.sh install ubuntu
./svc.sh start
trap - EXIT
