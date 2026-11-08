#!/usr/bin/env python3
"""Keep Lake Build progress while omitting successful Stacks diagnostics."""
import re
import sys

# Lake 4.35 Build.Run.Monitor.reportJob emits one non-ANSI status line
# followed by that job's diagnostic entries.
JOB = re.compile(r'^([✔ℹ⚠✖⊘]) \[\d+/\d+\](?: \(Optional\))? (\w+) (\S+)')
STACKS = re.compile(r'^Stacks(?:Core|Frontier)?(?:[.:/]|$)')
END = ('Build completed ', 'Nothing to build.', 'Some required targets logged failures:',
       'All targets up-to-date ', 'error:', 'timeout:', '::')


def filter_log(source, destination):
    stacks = dropping = False
    for line in source:
        if job := JOB.match(line):
            icon, action, target = job.groups()
            stacks = icon in '✔ℹ⚠' and STACKS.match(target) is not None
            dropping = False
            if stacks:
                line = '✔' + line[1:]
            # Verbose mode also reports internal jobs which did no work and
            # emitted no diagnostics. Replay and other progress stay visible.
            if line.startswith('✔') and action in ('Ran', 'Reused'):
                continue
        elif line.startswith(END):
            stacks = dropping = False
        elif stacks:
            dropping = dropping or line.startswith(('warning: ', 'info: ', 'trace: '))
            if dropping:
                continue
        destination.write(line)


if __name__ == '__main__':
    filter_log(sys.stdin, sys.stdout)
