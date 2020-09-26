# tasks-analyzer.py
# SPDX-License-Identifier: GPL-2.0
#
# Usage:
#
#     perf record -e sched:sched_switch,sched:sched_migrate_task -a -- sleep 10
#     perf script report task-analyzer
#
# Arguments:
#
#     --rename-comms <pid>:<newname>[,<pid>:<newname>]
#               Allows to rename tasknames (comm) based on the process id. This
#               is helpful for usecases where several Python interpreters are
#               executed and script prints just 'python' without a pleasant way
#               to differentiate.
#               This option is also quite handy to shorten the name of a task.
#               --rename-comms 1:init,2:kthreadder
#
#
# Combined:
#
#     perf script task-analyzer -e sched:sched_switch,sched:sched_migrate_task -a -- sleep 10
#
# Hagen Paul Pfeifer <hagen@jauu.net>

from __future__ import print_function
import sys
import os
import string
import argparse
import decimal


sys.path.append(os.environ['PERF_EXEC_PATH'] +
                '/scripts/python/Perf-Trace-Util/lib/Perf/Trace')
from perf_trace_context import *
from Core import *


def _parse_args():
    global args
    parser = argparse.ArgumentParser(description="Analyze tasks behavior")
    parser.add_argument(
        "--summary",
        action='store_true',
        help='print all tasks, record len and other information and exit')
    parser.add_argument(
        "--ns",
        action='store_true',
        help='show timestamps in nanoseconds')
    parser.add_argument(
        "--filter-comms",
        default=None,
        help='filter out unneeded tasks by name')
    parser.add_argument(
        "--filter-pids",
        default=None,
        help='filter out unneeded tasks by pid')
    parser.add_argument(
        "--limit-to-cpu",
        help='show only tasks executed on particular CPU')
    parser.add_argument(
        "--limit-to-pids",
        default=None,
        help='allow to show only subset of tasks (--limit-to-comms 1,2')
    parser.add_argument(
        "--limit-to-comms",
        default=None,
        help='allow to show only subset of tasks (--limit-to-comms systemd,dbus-daemon')
    parser.add_argument(
        "--highlight-comms",
        default=None,
        help='colorize special tasks, e.g. --highlight-comms systemd:red,dbus-daemon:yellow')
    parser.add_argument(
        "--rename-comms",
        default='',
        help='rename task names by using pid (<pid>:<newname>[,<pid>:<newname>]')
    args = parser.parse_args()
    args.pid_renames = dict()
    for rename_tuple in args.rename_comms.split(','):
        pid_name = rename_tuple.split(':')
        if len(pid_name) != 2:
            continue
        args.pid_renames[int(pid_name[0])] = pid_name[1]


def _init_db():
    global db
    db = dict()
    db['running'] = dict()
    db['waiting'] = dict()


def trace_begin():
    _parse_args()
    _init_db()
    _print_header()

def trace_end():
    print (sys.version)


class Task(object):

    def __init__(self, tid, cpu, comm):
        self.tid = tid
        self.cpu = cpu
        self.comm = comm
        self.pid = None
        self.time_in = None
        self.time_out = None

    def schedule_in_at(self, time):
        self.time_in = time

    def schedule_out_at(self, time):
        assert(self.time_in)
        self.time_out = time

    def runtime(self, unit='us'):
        assert(unit == 'us')
        assert(self.time_out)
        return (self.time_out - self.time_in) * decimal.Decimal(1e6)

    def update_pid(self, pid):
        self.pid = pid


def task_id(pid, cpu):
    return '{}-{}'.format(pid, cpu)


def filter_non_printable(unfiltered):
    """ comm contains strange code like '\x00000'
    Filer these out for now"""
    filtered = ""
    for char in unfiltered:
        if char not in string.printable: continue
        filtered += char
    return filtered

LEN_TIME = 16
LEN_CPU = 4
LEN_PID = 8
LEN_TID = 8
LEN_COMM = 16
# allows 999 seconds to display, should be
# enough for all -a recorings
LEN_DURATION = 13

def _fmt_header():
    fmt  = '{{:>{}}}'.format(LEN_TIME)
    fmt += ' {{:>{}}}'.format(LEN_CPU + 2)
    fmt += ' {{:>{}}}'.format(LEN_PID)
    fmt += ' {{:>{}}}'.format(LEN_TID)
    fmt += ' {{:>{}}}'.format(LEN_COMM)
    fmt += ' {{:>{}}}'.format(LEN_DURATION)
    return fmt

def _fmt_body():
    time_precision = 6 if not args.ns else 9
    fmt  = '{{:{}.{}f}}'.format(LEN_TIME, time_precision)
    fmt += ' [{{:0{}d}}]'.format(LEN_CPU)
    fmt += ' {{: {}d}}'.format(LEN_PID)
    fmt += ' {{: {}d}}'.format(LEN_TID)
    fmt += ' {{: >{}}}'.format(LEN_COMM)
    fmt += ' {{:{}.3f}}'.format(LEN_DURATION)
    return fmt

def _print_header():
    fmt = _fmt_header()
    print(fmt.format('TASK-START-TIME', 'CPU', 'PID', 'TID', 'COMM', 'RUNTIME [us]'))


def _print_task_finish(task):
    fmt = _fmt_body()
    print(fmt.format(task.time_in, task.cpu, task.pid, task.tid, task.comm, task.runtime(unit='us')))

def _handle_task_finish(tid, cpu, time, perf_sample_dict):
    global db
    if tid == 0:
        return
    _id = task_id(tid, cpu)
    if _id not in db['running']:
        # may happen, if we missed the switch to
        # event. Seen in combination with --exclude-perf
        # where the start is filtered out, but not the
        # switched in. Probably a bug in exclude-perf
        # option.
        return
    task = db['running'][_id]
    task.schedule_out_at(time)

    # record TID, during schedule in the TID
    # is not available, update now
    pid = int(perf_sample_dict['sample']['pid'])
    task.update_pid(pid)
    db['waiting'][_id] = task
    del db['running'][_id]

    _print_task_finish(task)



def _handle_task_start(tid, cpu, comm, time):
    global db
    if tid == 0:
        return
    if tid in args.pid_renames:
        comm = args.pid_renames[tid]
    _id = task_id(tid, cpu)
    if _id in db['running']:
        # handle corner cases where already running tasks
        # are switched-to again - saw this via --exclude-perf
        # recorded traces. We simple ignore this "second start"
        # event.
        return
    assert(_id not in db['running'])
    if _id in db['waiting']:
        task = db['waiting'][_id]
    else:
        task = Task(tid, cpu, comm)
    task.schedule_in_at(time)
    db['running'][_id] = task

def time_to_internal(time_ns):
    """ to prevent float rounding errors the internal
    for format is based on decimals.
    """
    return decimal.Decimal(time_ns) / decimal.Decimal(1e9)


def sched__sched_switch(event_name, context, common_cpu,
                        common_secs, common_nsecs, common_pid, common_comm,
                        common_callchain, prev_comm, prev_pid, prev_prio, prev_state,
                        next_comm, next_pid, next_prio, perf_sample_dict):

    # cleanup comm strings
    time = time_to_internal(perf_sample_dict['sample']['time'])
    next_comm = filter_non_printable(next_comm.decode("utf-8"))

    _handle_task_finish(prev_pid, common_cpu, time, perf_sample_dict)
    _handle_task_start(next_pid, common_cpu, next_comm, time)


def trace_unhandled(event_name, context, event_fields_dict, perf_sample_dict):
    pass
