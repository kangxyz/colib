import { directWebhook as upstream } from './upstream.js'

// The pinned upstream handler verifies the signature of the original request
// before queueing it. This filter only narrows the requests sent to it.
export function isDependencyWarmup(event) {
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
    && job?.head_branch === 'main'
    && job.workflow_name === 'Dependency warmup'
    && job.name === 'Compile dependency modules'
    && Array.isArray(job.labels)
    && job.labels.length === 1
    && job.labels[0] === 'colib-dependency-warmup'
}

export function directWebhook(event, context) {
  if (!isDependencyWarmup(event)) return { statusCode: 202, body: 'Event ignored' }
  return upstream(event, context)
}
