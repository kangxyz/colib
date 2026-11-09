import { directWebhook as upstream } from './upstream.js'

const highJobs = new Map([
  ['Colib CI', ['lean / Build', 'lean / Test, lint and axiom audit']],
  ['Colib split CI', ['Build dependencies']],
  ['Dependency warmup', ['Compile dependency modules']],
  ['EC2 runner pilot', ['probe', 'Verify runner-local handoff']]
])
const standardJobs = ['lean / Build', 'lean / Test, lint and axiom audit']

// The pinned upstream handler verifies the signature of the original request
// before queueing it. This filter only narrows the requests sent to it.
export function isColibEc2Job(event) {
  const eventName = Object.entries(event.headers ?? {}).find(
    ([key]) => key.toLowerCase() === 'x-github-event'
  )?.[1]
  if (eventName !== 'workflow_job' || typeof event.body !== 'string') return false

  let payload
  try {
    payload = JSON.parse(event.isBase64Encoded ? Buffer.from(event.body, 'base64') : event.body)
  } catch {
    return false
  }
  const job = payload?.workflow_job
  return payload?.action === 'queued'
    && payload.repository?.full_name === 'kangxyz/colib'
    && payload.repository?.default_branch === 'main'
    && payload.sender?.login === 'kangxyz'
    && typeof job?.head_branch === 'string' && job.head_branch.length > 0
    && Array.isArray(job.labels)
    && job.labels.length === 1
    && ((job.labels[0] === 'colib-dependency-warmup' && highJobs.get(job.workflow_name)?.includes(job.name) === true)
      || (job.labels[0] === 'colib-standard-ec2' && job.workflow_name === 'Colib split CI' && standardJobs.includes(job.name)))
}

export function directWebhook(event, context) {
  if (!isColibEc2Job(event)) return { statusCode: 202, body: 'Event ignored' }
  return upstream(event, context)
}
