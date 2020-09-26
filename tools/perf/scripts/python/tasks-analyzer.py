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

# ASCII color sequences
C_GREY   = '\033[90m'
C_RED    = '\033[91m'
C_GREEN  = '\033[92m'
C_YELLOW = '\033[93m'
C_BLUE   = '\033[94m'
C_VIOLET = '\033[95m'
C_RESET  = '\033[0m'

def _check_color():
    """ implement auto-mode (aka isatty()) the remaining modes"""
    if sys.stdout.isatty() and args.stdio_color != 'never':
        return
    global C_GREY, C_RED, C_GREEN, C_YELLOW, C_BLUE, C_VIOLET, C_RESET
    C_GREY = C_RED = C_GREEN = C_YELLOW = C_BLUE =  C_VIOLET = C_RESET = ''


# py2/py3 compatibilty layer, see PEP469
try:
    dict.iteritems
except AttributeError:
    # py3
    def itervalues(d):
        return iter(d.values())
    def iteritems(d):
        return iter(d.items())
else:
    # py2
    def itervalues(d):
        return d.itervalues()
    def iteritems(d):
        return d.iteritems()


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
        "--filter-tasks",
        default=[],
        help='filter out unneeded tasks by tid, pid or processname. (--filter-task tid, comm )')
    parser.add_argument(
        "--limit-to-tasks",
        default=[],
        help='show only subset of tasks (--limit-to-task tid,comm)')
    parser.add_argument(
        "--highlight-comms",
        default='',
        help='colorize special tasks, e.g. --highlight-comms systemd:red,dbus-daemon:yellow' +
             ' highlight string can be a substring. A : must not be part of the string. Case sensitive')
    parser.add_argument(
        "--highlight-tids",
        default='',
        help='colorize special tasks, e.g. --highlight-tids 1:red,2:yellow')
    parser.add_argument(
        "--highlight-pids",
        default='',
        help='colorize special tasks, e.g. --highlight-tids 1:red,2:yellow')
    parser.add_argument(
        "--rename-comms-by-tid",
        default='',
        help='rename task names by using tid (<tid>:<newname>[,<tid>:<newname>]')
    parser.add_argument(
        "--stdio-color",
        default='auto',
        choices=['always', 'never', 'auto'],
        help='always, never or auto, allowing configuring color output via the command line')
    args = parser.parse_args()
    args.tid_renames = dict()

    argument_filter_sanity_check()


    if args.filter_tasks:
        args.filter_tasks = args.filter_tasks.split(",")
    if args.limit_to_tasks:
        args.limit_to_tasks = args.limit_to_tasks.split(",")

    for rename_tuple in args.rename_comms_by_tid.split(','):
        tid_name = rename_tuple.split(':')
        if len(tid_name) != 2:
            continue
        args.tid_renames[int(tid_name[0])] = tid_name[1]
    args.highlight_comms_map = dict()
    for highlight_comms_tuple in args.highlight_comms.split(','):
        comm_color_map = highlight_comms_tuple.split(':')
        if len(comm_color_map) != 2:
            continue
        args.highlight_comms_map[comm_color_map[0]] = comm_color_map[1]

    args.highlight_pids_map = dict()
    for highlight_pids_tuple in args.highlight_pids.split(','):
        pids_color_map = highlight_pids_tuple.split(':')
        if len(pids_color_map) != 2:
            continue
        args.highlight_pids_map[int(pids_color_map[0])] = pids_color_map[1]

def time_uniter(unit):
    picker = {
        's' : 1,
        'ms' : 1e3,
        'us' : 1e6,
        'ns' : 1e9,
    }
    return picker[unit]

def color_by_name(name):
    picker = {
        'grey' : C_GREY,
        'red' : C_RED,
        'green' : C_GREEN,
        'yellow' : C_YELLOW,
        'blue' : C_BLUE,
        'violet' : C_VIOLET
    }
    return picker.get(name.lower(), C_VIOLET)

def _init_db():
    global db
    db = dict()
    db['running'] = dict()
    db['cpu'] = dict()
    db['tid'] = dict()
    db['global'] = list()


def trace_begin():
    _parse_args()
    _check_color()
    _init_db()
    _print_header()

def median(numbers):
    """ phython3 hat statistics module - we have nothing"""
    n = len(numbers)
    index = n // 2
    if n % 2: return sorted(numbers)[index]
    return sum(sorted(numbers)[index - 1:index + 1]) / 2

def mean(numbers):
    return sum(numbers) / len(numbers)


class Distances(object):

    def __init__(self):
        self._last_finish = None
        self._distances = list()

    def feed(self, task):
        """ chronological ordering, feed does not not do reordering """
        if not self._last_finish:
            self._last_finish = task.time_out(unit='us')
            return
        time_in_us = task.time_in(unit='us')
        assert(time_in_us >= self._last_finish)
        self._distances.append(float(time_in_us - self._last_finish))
        self._last_finish = task.time_out(unit='us')

    def last_gap(self, unit='us'):
        assert(unit == 'us')
        assert(len(self._distances) > 0)
        return self._distances[-1]

    def __len__(self):
        return len(self._distances)

    def values(self):
        return self._distances

    def min(self):
        return min(self._distances)

    def max(self):
        return max(self._distances)

    def mean(self):
        return mean(self._distances)

    def median(self):
        return median(self._distances)

    def format(self):
        if len(self._distances) < 2:
            fmt = '{:>16} {:>16} {:>16}'
            return fmt.format("-", "-", "-")
        else:
            fmt = '{:>16.2f} {:>16.2f} {:>16.2f}'
            return fmt.format(self.max(), self.min(), self.mean())


class Summary(object):

    # cluster 1 - task general info
    FMT_TASK_INFO_VAL = "{:>8} {:>8} {:>16}"
    FMT_TASK_INFO_L2 = "{:>8} {:>8} {:>16}"
    FMT_TASK_INFO_L1  = "{:>34}"
    # cluster 2 - runtimes (max, min, avg, ...) incl executions
    FMT_RUNTIME_INFO_VAL = "{:>8} {:14.1f} {} {:16.3f} {:16.3f} {:10.3f} {:10.3f}"
    FMT_RUNTIME_INFO_L2 = "{:>8} {:>14}  {:>16} {:>16} {:>10} {:>10}"
    FMT_RUNTIME_INFO_L1  = "{:>80}"
    # cluster 3 - distances (max, min, avg)
    FMT_DISTANCE_INFO_VAL = "{} {}"
    FMT_DISTANCE_INFO_L2 = "{:>30}"
    FMT_DISTANCE_INFO_L1  = "{:>40}"

    def __init__(self, db):
        self._db = db

    def _l1_header(self):
        fmt = Summary.FMT_TASK_INFO_L1 + Summary.FMT_RUNTIME_INFO_L1 + Summary.FMT_DISTANCE_INFO_L1
        out = fmt.format("Task Information", "Runtime Information [us]", "Inter Task Gap")
        print(out)

    def _l2_header(self):
        out  = Summary.FMT_TASK_INFO_L2.format("PID", "TID", "Comm")
        out += Summary.FMT_RUNTIME_INFO_L2.format("Runs", "Accumulated", "Max", "Min", "Mean", "Median")
        out += Summary.FMT_DISTANCE_INFO_L2.format("Gap")
        print(out)

    def _task_stats(self):
        fmt = Summary.FMT_TASK_INFO_VAL + Summary.FMT_RUNTIME_INFO_VAL + Summary.FMT_DISTANCE_INFO_VAL
        for tid in sorted(db['tid']):
            color_one_sample = C_GREY
            color_reset = C_RESET
            no_executed = 0
            runtimes = list()

            distances = Distances()
            for task in db['tid'][tid]:
                pid = task.pid
                comm = task.comm
                no_executed += 1
                runtimes.append(float(task.runtime()))
                distances.feed(task)

            if len(runtimes) > 1:
                color_one_sample = ""
                color_reset = ''
            time_sum = sum(runtimes)
            time_max = max(runtimes)
            time_min = min(runtimes)
            time_mean = mean(runtimes)
            time_median = median(runtimes)
            distances_str = distances.format()
            s = fmt.format(pid, tid, comm,
                           no_executed, time_sum, color_one_sample, time_max, time_min, time_mean, time_median,
                           distances_str, color_reset)
            print(s)

    def print(self):
        print("\nSummary")
        self._l1_header()
        self._l2_header()
        self._task_stats()





def trace_end():
    if args.summary:
        Summary(db).print()
    

class Task(object):

    def __init__(self, id, tid, cpu, comm):
        self.id = id
        self.tid = tid
        self.cpu = cpu
        self.comm = comm
        self.pid = None
        # in Decimal seconds
        self._time_in = None
        self._time_out = None

    def schedule_in_at(self, time):
        """set the time where the task was scheduled in"""
        self._time_in = time

    def schedule_out_at(self, time):
        """set the time where the task was scheduled out"""
        assert(self.time_in)
        self._time_out = time

    def time_out(self, unit='s'):
        """return time where a given task was scheduled out"""
        factor = time_uniter(unit)
        return self._time_out * decimal.Decimal(factor)

    def time_in(self, unit='s'):
        """return time where a given task was scheduled in"""
        factor = time_uniter(unit)
        return self._time_in * decimal.Decimal(factor)

    def runtime(self, unit='us'):
        assert(unit == 'us')
        assert(self._time_out)
        return (self._time_out - self._time_in) * decimal.Decimal(1e6)

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
LEN_GAP_TID_LAST = 13

def _fmt_header():
    fmt  = '{{:>{}}}'.format(LEN_TIME)
    fmt += ' {{:>{}}}'.format(LEN_TIME)
    fmt += ' {{:>{}}}'.format(LEN_CPU + 2)
    fmt += ' {{:>{}}}'.format(LEN_PID)
    fmt += ' {{:>{}}}'.format(LEN_TID)
    fmt += ' {{:>{}}}'.format(LEN_COMM)
    fmt += ' {{:>{}}}'.format(LEN_DURATION)
    fmt += ' {{:>{}}}'.format(LEN_GAP_TID_LAST)
    return fmt

def _fmt_body():
    time_precision = 6 if not args.ns else 9
    us_precision = 0 if not args.ns else 3
    fmt  = '{{:{}.{}f}}'.format(LEN_TIME, time_precision)
    fmt += ' {{:{}.{}f}}'.format(LEN_TIME, time_precision)
    fmt += ' [{{:0{}d}}]'.format(LEN_CPU)
    fmt += ' {{}}{{: {}d}}{{}}'.format(LEN_PID)
    fmt += ' {{}}{{: {}d}}{{}}'.format(LEN_TID) 
    fmt += ' {{}}{{: >{}}}{{}}'.format(LEN_COMM)
    fmt += ' {{:{}.{}f}}'.format(LEN_DURATION, us_precision)
    fmt += ' {{:{}.{}f}}'.format(LEN_GAP_TID_LAST, us_precision)
    return fmt

def _print_header():
    fmt = _fmt_header()
    header =('SWITCHED-OUT', 'SWITCHED-IN', 'CPU', 'PID' )
    header += ('TID',)
    header += ('COMM', 'RUNTIME [us]', 'GAP LAST TID[us]')   
    print(fmt.format(*header))


def _print_task_finish(task):
    fmt = _fmt_body()
    comm = task.comm
    c_comm_color = ''
    c_comm_reset = ''
    for search_key in args.highlight_comms_map:
        if not search_key in comm:
            continue
        c_comm_color = color_by_name(args.highlight_comms_map[search_key])
        c_comm_reset =  C_RESET

    c_pid_color = ''
    c_pid_reset = ''
    if task.pid in args.highlight_pids_map:
        c_pid_color = color_by_name(args.highlight_pids_map[task.pid])
        c_pid_reset =  C_RESET

    for search_key in args.highlight_comms_map:
        if not search_key in comm:
            continue
        c_comm_color = color_by_name(args.highlight_comms_map[search_key])
        c_comm_reset =  C_RESET

    # grey-out entries if PID == TID, they
    # are identical, no threaded model so the
    # thread id (tid) do not matter
    c_tid_color = ''
    c_tid_reset = ""
    if task.pid == task.tid:
        c_tid_color = C_GREY
        c_tid_reset =  C_RESET

    # calculate gap for a given TID
    last_gap = -1.0
    if task.tid in db['tid']:
        # get last task of tid
        last_tid_task = db['tid'][task.tid][-1]
        # feed the distance calulate, last in tid db
        # and second the current one
        distance_gap_tid = Distances()
        distance_gap_tid.feed(last_tid_task)
        distance_gap_tid.feed(task)
        last_gap = distance_gap_tid.last_gap(unit='us')

    body = (task.time_out(), task.time_in(), task.cpu,c_pid_color, task.pid, c_pid_reset)
    body+= (c_tid_color , task.tid, c_tid_reset) 
    body+= (c_comm_color, comm, c_comm_reset,task.runtime(unit='us'), last_gap)
    print(fmt.format(*body))


def _record_cleanup(_list):
    """no need to store more then one element if --summarize
    is not enabled
    """
    if not args.summary and len(_list) > 1:
        _list = _list[len(_list)-1:] 

def _record_by_tid(task):
    global db
    tid = task.tid
    if tid not in db['tid']:
        db['tid'][tid] = list()
    db['tid'][tid].append(task)
    _record_cleanup(db['tid'][tid])

def _record_by_cpu(task):
    global db
    cpu = task.cpu
    if cpu not in db['cpu']:
        db['cpu'][cpu] = list()
    db['cpu'][cpu].append(task)
    _record_cleanup(db['cpu'][cpu])

def _record_global(task):
    """ record all executed task, ordered by finish time"""
    global db
    db['global'].append(task)
    _record_cleanup(db['global'])

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
    #db['waiting'][_id] = task
    del db['running'][_id]

    _print_task_finish(task)

    _record_by_tid(task)
    _record_by_cpu(task)
    _record_global(task)

def _handle_task_start(tid, cpu, comm, time):
    global db
    if tid == 0:
        return
    if tid in args.tid_renames:
        comm = args.tid_renames[tid]
    _id = task_id(tid, cpu)
    if _id in db['running']:
        # handle corner cases where already running tasks
        # are switched-to again - saw this via --exclude-perf
        # recorded traces. We simple ignore this "second start"
        # event.
        return
    assert(_id not in db['running'])
    task = Task(_id, tid, cpu, comm)
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

    # ignore common_secs & common_nsecs cause we need
    # high res timestamp anyway, using the raw value is
    # faster
    time = time_to_internal(perf_sample_dict['sample']['time'])
    next_comm = filter_non_printable(next_comm)

    _handle_task_finish(prev_pid, common_cpu, time, perf_sample_dict)
    _handle_task_start(next_pid, common_cpu, next_comm, time)


def trace_unhandled(event_name, context, event_fields_dict, perf_sample_dict):
    pass
