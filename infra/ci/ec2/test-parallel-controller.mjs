import assert from 'node:assert/strict'
import { test } from 'node:test'
import { listPendingRuns, reconcile } from './parallel-controller.mjs'

function fixture() {
  const runs = new Map()
  const jobs = new Map()
  const leases = new Map()
  const instances = new Map()
  const launched = []
  const registered = []
  const disposed = []
  const orphans = []
  let now = 1_800_000_000

  function run(id, branch, options = {}) {
    const value = {
      id, run_attempt: 1, head_branch: branch, status: 'queued', event: 'push',
      path: '.github/workflows/ci.yml', actor: { login: 'kangxyz' },
      triggering_actor: { login: 'kangxyz' }, repository: { full_name: 'kangxyz/colib' },
      head_repository: { full_name: 'kangxyz/colib' }, ...options
    }
    runs.set(id, value)
    jobs.set(id, [{
      name: 'lean / Build', status: 'queued', labels: [`colib-ci-run-${id}-${value.run_attempt}`]
    }])
    return value
  }

  const io = {
    listLeases: async () => structuredClone([...leases.values()]),
    saveLease: async (lease, fresh) => {
      if (fresh) assert(!leases.has(lease.key))
      leases.set(lease.key, structuredClone(lease))
    },
    run: async id => runs.get(id),
    pendingRuns: async () => [...runs.values()].filter(run => run.status !== 'completed'),
    jobs: async run => jobs.get(run.id),
    findInstance: async key => instances.get(key),
    instanceState: async id => [...instances.values()].find(instance => instance.InstanceId === id)?.state,
    launch: async lease => {
      const instance = { InstanceId: `i-${lease.key}`, state: 'running' }
      assert(!instances.has(lease.key), 'a duplicate launch would create a second machine')
      instances.set(lease.key, instance)
      launched.push(lease.key)
      return instance
    },
    register: async lease => registered.push(lease.key),
    dispose: async lease => {
      instances.delete(lease.key)
      disposed.push(lease.key)
    },
    orphaned: async (lease, reason) => orphans.push([lease.key, reason]),
    warn: () => {}
  }

  return {
    io, runs, jobs, leases, instances, launched, registered, disposed, orphans, run,
    advance: seconds => { now += seconds },
    tick: () => reconcile(io, { now, limit: 2, templateVersion: '1' })
  }
}

test('two branches get private instances; the third waits and Test retains the Build instance', async () => {
  const f = fixture()
  const first = f.run(100, 'work/a')
  const second = f.run(101, 'work/b')
  f.run(102, 'work/c')
  await f.tick()
  assert.deepEqual(f.launched, ['100-1', '101-1'])
  assert.deepEqual(f.registered, ['100-1', '101-1'])

  first.status = 'in_progress'
  second.status = 'in_progress'
  f.jobs.get(second.id)[0].status = 'in_progress'
  f.jobs.get(first.id)[0].status = 'completed'
  f.jobs.get(first.id).push({
    name: 'lean / Test, lint and axiom audit', status: 'queued', labels: ['colib-ci-run-100-1']
  })
  f.advance(20 * 60)
  await f.tick()
  assert.deepEqual(f.launched, ['100-1', '101-1'])
  assert.equal(f.instances.get('100-1').InstanceId, 'i-100-1')

  second.status = 'completed'
  await f.tick()
  assert.deepEqual(f.disposed, ['101-1'])
  assert.deepEqual(f.launched, ['100-1', '101-1', '102-1'])
})

test('a queued run missing from the status-filtered list gets its turn', async () => {
  const f = fixture()
  const active = f.run(100, 'work/active')
  await f.tick()
  active.status = 'in_progress'
  f.jobs.get(active.id)[0].status = 'in_progress'

  const completed = f.run(99, 'work/completed', { status: 'completed' })
  const main = f.run(101, 'main')
  const later = f.run(102, 'work/later')
  const filteredOnly = f.run(103, 'work/filtered-only')
  const workflow = '/actions/workflows/ci.yml/runs'
  const responses = new Map([
    [`${workflow}?per_page=100&page=1`, [later, main, active, completed]],
    [`${workflow}?status=queued&per_page=100&page=1`, [filteredOnly, later, { ...completed, status: 'queued' }]],
    [`${workflow}?status=in_progress&per_page=100&page=1`, [active]]
  ])
  f.io.pendingRuns = () => listPendingRuns(async path => {
    assert(responses.has(path), path)
    return { workflow_runs: responses.get(path) }
  })
  assert.deepEqual((await f.io.pendingRuns()).map(run => run.id), [102, 101, 100, 103])
  await f.tick()
  assert.deepEqual(f.launched, ['100-1', '101-1'])
})

test('a lost launch reply is adopted and a terminated attempt releases the registration', async () => {
  const f = fixture()
  const run = f.run(200, 'work/one')
  const launch = f.io.launch
  f.io.launch = async lease => {
    await launch(lease)
    throw new Error('simulated lost EC2 response')
  }
  await f.tick()
  assert(!f.leases.get('200-1').instanceId)
  await f.tick()
  assert.deepEqual(f.launched, ['200-1'])
  assert.deepEqual(f.registered, ['200-1'])
  run.status = 'completed'
  await f.tick()
  assert.deepEqual(f.disposed, ['200-1'])
  assert.equal(f.leases.get('200-1').retired, true)
})

test('cancellation during a lost launch response waits for EC2 visibility before releasing the lease', async () => {
  const f = fixture()
  const run = f.run(300, 'work/cancelled')
  const launch = f.io.launch
  f.io.launch = async lease => {
    await launch(lease)
    throw new Error('simulated lost EC2 response')
  }
  await f.tick()
  run.status = 'completed'
  const find = f.io.findInstance
  f.io.findInstance = async () => undefined
  f.advance(60)
  await f.tick()
  assert(!f.leases.get('300-1').retired)
  f.io.findInstance = find
  await f.tick()
  assert.deepEqual(f.disposed, ['300-1'])
})

test('a lost assigned runner cannot be replaced under the same attempt', async () => {
  const f = fixture()
  f.run(400, 'work/lost')
  await f.tick()
  f.instances.get('400-1').state = 'terminated'
  await f.tick()
  await f.tick()
  assert.deepEqual(f.launched, ['400-1'])
  assert.deepEqual(f.orphans, [['400-1', 'the assigned instance is unavailable']])
  f.run(400, 'work/lost', { run_attempt: 2 })
  await f.tick()
  assert.deepEqual(f.launched, ['400-1', '400-2'])
})

test('the controller never provisions for a PR, another workflow, a legacy label or Test alone', async () => {
  const f = fixture()
  f.run(500, 'work/pr', { event: 'pull_request' })
  f.run(501, 'work/wrong-workflow', { path: '.github/workflows/other.yml' })
  f.run(502, 'work/legacy')
  f.jobs.get(502)[0].labels = ['colib-dependency-warmup']
  f.run(503, 'work/test-only')
  f.jobs.get(503)[0].name = 'lean / Test, lint and axiom audit'
  f.run(504, 'work/other-owner', { actor: { login: 'someone-else' } })
  await f.tick()
  assert.deepEqual(f.launched, [])
  assert.equal(f.leases.size, 0)
})
