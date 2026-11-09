import { sign } from 'node:crypto'

const owner = 'kangxyz'
const repository = 'colib'
const fullRepository = `${owner}/${repository}`
const buildName = 'lean / Build'
const bootTimeout = 15 * 60
const missingGrace = 2 * 60
const retention = 7 * 24 * 60 * 60

const runKey = run => `${run.id}-${run.run_attempt}`
const label = key => `colib-ci-run-${key}`
const runnerName = lease => `${label(lease.key)}-${lease.instanceId}`

function trusted(run) {
  return run && Number.isSafeInteger(run.id) && run.id > 0
    && Number.isSafeInteger(run.run_attempt) && run.run_attempt > 0
    && run.path === '.github/workflows/ci.yml'
    && run.repository?.full_name === fullRepository && run.head_repository?.full_name === fullRepository
    && run.actor?.login === owner && run.triggering_actor?.login === owner
    && typeof run.head_branch === 'string' && run.head_branch.length > 0
    && (run.event === 'push' || run.event === 'workflow_dispatch')
}

function queuedBuild(jobs, key) {
  return jobs.some(job => job.name === buildName && job.status === 'queued'
    && job.labels?.length === 1 && job.labels[0] === label(key))
}

// Only the scheduled controller allocates slots. A consistent lease scan counts
// launches before EC2 discovery, and the EC2 client token covers a lost reply.
export async function reconcile(io, { now, limit, templateVersion, canContinue = () => true }) {
  const leases = new Map((await io.listLeases()).map(lease => [lease.key, lease]))
  let occupied = [...leases.values()].filter(lease => !lease.retired).length

  async function retire(lease, reason) {
    if (lease.instanceId) await io.dispose(lease)
    if (reason) await io.orphaned(lease, reason)
    await io.saveLease({ ...lease, retired: true, expiresAt: now + retention })
    occupied -= 1
  }

  async function configure(lease) {
    if (!lease.registered) {
      await io.register(lease)
      lease.registered = true
      await io.saveLease(lease)
    }
  }

  async function provision(lease, instance) {
    if (!instance) {
      lease.launchAttemptedAt = now
      await io.saveLease(lease)
      instance = await io.launch(lease)
    }
    lease.instanceId = instance.InstanceId
    lease.launchedAt = now
    await io.saveLease(lease)
    await configure(lease)
  }

  for (const lease of leases.values()) {
    if (lease.retired) continue
    if (!canContinue()) return
    try {
      const run = await io.run(lease.runId)
      if (!trusted(run) || run.run_attempt !== lease.attempt || run.status === 'completed') {
        // A process can stop after EC2 accepted the request but before it saved
        // the ID. Look up that instance even when the run has since ended.
        if (!lease.instanceId) {
          lease.instanceId = (await io.findInstance(lease.key))?.InstanceId
          if (!lease.instanceId && now - (lease.launchAttemptedAt ?? 0) < missingGrace) continue
        }
        await retire(lease)
        continue
      }
      if (!lease.instanceId) {
        const instance = await io.findInstance(lease.key)
        if (instance || queuedBuild(await io.jobs(run), lease.key)) {
          await provision(lease, instance)
        } else if (now - (lease.launchAttemptedAt ?? 0) >= missingGrace) {
          await retire(lease, 'Build left the queue without a runner')
        }
        continue
      }

      const state = await io.instanceState(lease.instanceId)
      if (!state && now - lease.launchedAt < missingGrace) continue
      if (!['pending', 'running'].includes(state)) {
        await retire(lease, 'the assigned instance is unavailable')
      } else if (now - lease.launchedAt >= bootTimeout && queuedBuild(await io.jobs(run), lease.key)) {
        await retire(lease, 'Build did not start before the bootstrap deadline')
      } else {
        await configure(lease)
      }
    } catch (error) {
      io.warn(lease.key, error)
    }
  }

  if (occupied >= limit || !canContinue()) return
  const candidates = (await io.pendingRuns()).filter(trusted)
    .sort((left, right) => left.id - right.id)
  for (const run of candidates) {
    if (occupied >= limit || !canContinue()) break
    const key = runKey(run)
    if (leases.has(key)) continue
    try {
      if (!queuedBuild(await io.jobs(run), key)) continue
      const lease = { key, runId: run.id, attempt: run.run_attempt, templateVersion }
      // Count the reservation before awaiting a write whose response could be lost.
      occupied += 1
      leases.set(key, lease)
      await io.saveLease(lease, true)
      await provision(lease, await io.findInstance(lease.key))
    } catch (error) {
      io.warn(key, error)
    }
  }
}

async function githubRequest(path, token, { method = 'GET', body } = {}) {
  const response = await fetch(`https://api.github.com${path}`, {
    method,
    headers: {
      authorization: `Bearer ${token}`,
      accept: 'application/vnd.github+json',
      'x-github-api-version': '2022-11-28',
      ...(body ? { 'content-type': 'application/json' } : {})
    },
    body: body ? JSON.stringify(body) : undefined,
    signal: AbortSignal.timeout(7000)
  })
  if (response.status === 404 && method === 'GET') return null
  if (response.status === 404 && method === 'DELETE') return null
  if (!response.ok) throw new Error(`GitHub ${method} ${path} returned ${response.status}`)
  const content = await response.text()
  return content ? JSON.parse(content) : null
}

let installationToken

async function githubApp(ssm, GetParameterCommand, config, now) {
  if (installationToken?.expiresAt > now + 120) return installationToken
  const key = await ssm.send(new GetParameterCommand({ Name: config.GITHUB_KEY, WithDecryption: true }))
  const header = Buffer.from(JSON.stringify({ alg: 'RS256', typ: 'JWT' })).toString('base64url')
  const claims = Buffer.from(JSON.stringify({ iss: config.GITHUB_APP_ID, iat: now - 60, exp: now + 300 })).toString('base64url')
  const content = `${header}.${claims}`
  const signature = sign('RSA-SHA256', Buffer.from(content), Buffer.from(key.Parameter.Value, 'base64'))
  const jwt = `${content}.${signature.toString('base64url')}`
  const installation = await githubRequest(`/repos/${fullRepository}/installation`, jwt)
  if (installation?.account?.login !== owner || installation?.suspended_at) {
    throw new Error('Colib GitHub App installation is unavailable')
  }
  const access = await githubRequest(`/app/installations/${installation.id}/access_tokens`, jwt, {
    method: 'POST',
    body: { repositories: [repository], permissions: { administration: 'write', actions: 'read' } }
  })
  installationToken = { token: access.token, expiresAt: Date.parse(access.expires_at) / 1000 }
  return installationToken
}

async function pages(github, path, property) {
  const entries = []
  const separator = path.includes('?') ? '&' : '?'
  for (let page = 1; ; page += 1) {
    const response = await github(`${path}${separator}per_page=100&page=${page}`)
    const items = response?.[property]
    if (!Array.isArray(items)) throw new Error(`Missing GitHub ${property}`)
    entries.push(...items)
    if (items.length < 100) return entries
  }
}

export async function handler(_event, context) {
  const { EC2Client, DescribeInstancesCommand, RunInstancesCommand, TerminateInstancesCommand } = await import('@aws-sdk/client-ec2')
  const { SSMClient, GetParameterCommand, PutParameterCommand, DeleteParameterCommand } = await import('@aws-sdk/client-ssm')
  const { DynamoDBClient, ScanCommand, PutItemCommand } = await import('@aws-sdk/client-dynamodb')
  const config = process.env
  const now = Math.floor(Date.now() / 1000)
  const ec2 = new EC2Client()
  const ssm = new SSMClient()
  const dynamo = new DynamoDBClient()
  const auth = await githubApp(ssm, GetParameterCommand, config, now)
  const github = (path, options) => githubRequest(`/repos/${fullRepository}${path}`, auth.token, options)
  const tokenName = lease => `${config.RUNNER_TOKEN_PATH}/${lease.instanceId}`
  const instances = response => response.Reservations.flatMap(reservation => reservation.Instances)
  const environment = { Key: 'ghr:environment', Value: config.RUNNER_ENVIRONMENT }

  const io = {
    async listLeases() {
      const leases = []
      let cursor
      do {
        const page = await dynamo.send(new ScanCommand({
          TableName: config.LEASE_TABLE, ConsistentRead: true, ExclusiveStartKey: cursor
        }))
        leases.push(...(page.Items ?? []).map(item => JSON.parse(item.payload.S)))
        cursor = page.LastEvaluatedKey
      } while (cursor && Object.keys(cursor).length)
      return leases
    },
    async saveLease(lease, fresh = false) {
      await dynamo.send(new PutItemCommand({
        TableName: config.LEASE_TABLE,
        Item: {
          run_key: { S: lease.key },
          payload: { S: JSON.stringify(lease) },
          ...(lease.expiresAt ? { expires_at: { N: String(lease.expiresAt) } } : {})
        },
        ...(fresh ? { ConditionExpression: 'attribute_not_exists(run_key)' } : {})
      }))
    },
    run: id => github(`/actions/runs/${id}`),
    jobs: run => pages(github, `/actions/runs/${run.id}/attempts/${run.run_attempt}/jobs`, 'jobs'),
    async pendingRuns() {
      const workflow = '/actions/workflows/ci.yml/runs'
      return [
        ...await pages(github, `${workflow}?status=queued`, 'workflow_runs'),
        ...await pages(github, `${workflow}?status=in_progress`, 'workflow_runs')
      ]
    },
    async findInstance(key) {
      const response = await ec2.send(new DescribeInstancesCommand({ Filters: [
        { Name: `tag:${environment.Key}`, Values: [environment.Value] },
        { Name: 'tag:colib-ci-run', Values: [key] }
      ] }))
      const matches = instances(response)
      if (matches.length > 1) throw new Error('Multiple instances have the same lease')
      return matches[0]
    },
    async instanceState(id) {
      try {
        const response = await ec2.send(new DescribeInstancesCommand({ InstanceIds: [id] }))
        return instances(response)[0]?.State?.Name
      } catch (error) {
        if (error.name !== 'InvalidInstanceID.NotFound') throw error
        return undefined
      }
    },
    async launch(lease) {
      const response = await ec2.send(new RunInstancesCommand({
        ClientToken: label(lease.key),
        MinCount: 1,
        MaxCount: 1,
        LaunchTemplate: { LaunchTemplateId: config.LAUNCH_TEMPLATE, Version: lease.templateVersion },
        TagSpecifications: [{ ResourceType: 'instance', Tags: [
          environment, { Key: 'colib-ci-run', Value: lease.key }
        ] }]
      }))
      if (response.Instances.length !== 1) throw new Error('Expected one EC2 instance')
      return response.Instances[0]
    },
    async register(lease) {
      const token = await github('/actions/runners/registration-token', { method: 'POST' })
      try {
        await ssm.send(new PutParameterCommand({
          Name: tokenName(lease), Value: token.token, Type: 'SecureString', Overwrite: false
        }))
      } catch (error) {
        if (error.name !== 'ParameterAlreadyExists') throw error
      }
    },
    async dispose(lease) {
      try {
        await ec2.send(new TerminateInstancesCommand({ InstanceIds: [lease.instanceId] }))
      } catch (error) {
        if (error.name !== 'InvalidInstanceID.NotFound') throw error
      }
      try {
        await ssm.send(new DeleteParameterCommand({ Name: tokenName(lease) }))
      } catch (error) {
        if (error.name !== 'ParameterNotFound') throw error
      }
      const runners = await pages(github, '/actions/runners', 'runners')
      const runner = runners.find(item => item.name === runnerName(lease))
      if (runner) await github(`/actions/runners/${runner.id}`, { method: 'DELETE' })
    },
    orphaned: (lease, reason) => console.error(`Run ${lease.key} needs cancellation and a full rerun: ${reason}.`),
    warn: (key, error) => console.warn(`Lease ${key}: ${error.name}: ${error.message}`)
  }
  await reconcile(io, {
    now, limit: Number(config.RUNNER_LIMIT), templateVersion: config.TEMPLATE_VERSION,
    canContinue: () => context.getRemainingTimeInMillis() > 12000
  })
}
