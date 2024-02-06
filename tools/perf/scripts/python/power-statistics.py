# power-statistics.py - comprehensive perf power analyzer
# SPDX-License-Identifier: GPL-2.0
# Copyright (c) 2023, Hagen Paul Pfeifer <hagen@jauu.net>
# Licensed under the terms of the GNU GPL License version 2
#
# Usage:
#
#     sudo perf record -a -e sched:sched_switch,power:cpu_frequency,power:cpu_idle,irq:irq_handler_entry,timer:hrtimer_cancel,power:cpu_idle_miss -o /tmp/perf.out -- sleep 10
#     sudo chown $USER:$USER /tmp/perf.out
#     perf script -i /tmp/perf.out -s ~/src/code/linux/tools/perf/scripts/python/power-statistics.py -- --mode {$MODE}

from __future__ import print_function
import sys
import os
import string
import argparse
import enum
import decimal
import collections
import itertools
import statistics
import pprint
import signal
import types
import math
import json
import re


sys.path.append(
    os.environ["PERF_EXEC_PATH"] + "/scripts/python/Perf-Trace-Util/lib/Perf/Trace"
)
from perf_trace_context import *
from Core import *

class VERBOSETYPE(enum.IntEnum):
    DISABLE = 0
    EXPRESSING = 1

# Definition of possible ASCII color codes
_COLORS_FG = {
    "grey": "\033[90m",
    "red": "\033[91m",
    "green": "\033[92m",
    "yellow": "\033[93m",
    "blue": "\033[94m",
    "violet": "\033[95m",
    "black": "\033[30m",
}

_COLORS_BG = {
    "grey": "\033[47m",
    "red": "\033[41m",
    "green": "\033[42m",
    "yellow": "\033[103m",
    "blue": "\033[44m",
    "purple": "\033[105m",
    "orange": "\033[43m",
    "teal": "\033[106m",
}

_COLOR_RESET = "\033[0m"

# Some commands are happy for further analysis
# just print them randomly to enlight the reader
TIPS = [
    'To find for a given thread id (tid) all threads in this group, call "grep . /proc/<N>/task/*/comm"',
    'Use grep, ag, ripgrep and friends to filter for application names or pids of interrest',
    'Analysed perf.data files can be further analyzed via perf script to show all captured events in an unmodified way'
]


# (unsigned)-1 is wakeup event encoded.
POWER_WAKE_ID = 4294967295

# prevent broken pipe error for write() from piping
# the output of this script to head and friends
signal.signal(signal.SIGPIPE, signal.SIG_DFL)

# we account first and last event time globally
# because it is used in multiple (all?) modules
event_time_first = event_time_last = None

def args_check_color(args):
    global _COLORS
    """user enforced no-color or if stdout is no tty we disable colors"""
    if sys.stdout.isatty() and args.stdio_color != "never":
        return
    _COLORS = {
        "grey": "",
        "red": "",
        "green": "",
        "yellow": "",
        "blue": "",
        "violet": "",
        "reset": "",
    }


def parse_args():
    global args
    parser = argparse.ArgumentParser(description="Power Management Analyzer")
    parser.add_argument(
        "-m", "--mode",
        default="idle-cluster",
        const='idle-cluster',
        nargs='?',
        choices=['idle-cluster', 'task', 'timer', 'frequency', 'wakeups-timemap', 'idle-governor', 'all'],
    )
    parser.add_argument(
        "-C", "--cpu",
        default=None,
        type=int
    )
    parser.add_argument(
        "-v", "--verbose",
        action="count",
        default=0,
        help="enfore module to show more and detailed information"
    )
    parser.add_argument(
        "--highlight-tasks",
        default="",
        help="colorize special tasks by their pid/tid/comm."
        " E.g. --highlight-tasks 1:red,mutt:yellow"
        " Colors available: red,grey,yellow,blue,violet,green",
    )
    parser.add_argument(
        "--stdio-color",
        default="auto",
        choices=["always", "never", "auto"],
        help="always, never or auto, allowing configuring color output"
            " via the command line",
    )
    parser.add_argument(
        "--file-out",
        action='store_true',
        help="do not print the output to STDOUT, print into individual files, named after the module"
    )
    parser.add_argument(
        "--csv",
        action='store_true'
    )
    args = parser.parse_args()
    return args


def csv_sep(string):
    """prepares format string with ; in csv mode or whitespaces if not """
    if args.csv:
        substr = ";"
    else:
        substr = " "
    return string.replace("S", substr)


def csv_clean(string):
    """ removes leading & trailing whitespaces for each semicolom separated element"""
    if not args.csv:
        return string
    return ";".join([chunk.strip() for chunk in string.split(";")])


def section_header(input_string):
    total_width = 76
    padding = (total_width - len(input_string)) // 2
    return '=' * padding + " " + input_string + " " + '=' * padding


def str_cpu_zeroized(cpu):
    return f"{cpu:03d}"


def _task_id(pid, cpu):
    return "{}-{}".format(pid, cpu)


def _filter_non_printable(unfiltered):
    """comm names may contain loony chars like '\x00000'"""
    filtered = ""
    for char in unfiltered:
        if char not in string.printable:
            continue
        filtered += char
    return filtered


def time_convert(time_ns):
    """ convert time to Decimal and do bookkeeping """
    global event_time_first, event_time_last
    time = decimal.Decimal(time_ns) / decimal.Decimal(1e9)
    if not event_time_first:
        event_time_first = time
    event_time_last = time
    return time


def decimal_to_ms_rounded(time, quantize='0.001'):
    """ take Decimal in seconds, convert to ms and round to us granularity """
    ms = time * decimal.Decimal(1000.0)
    return ms.quantize(decimal.Decimal(quantize), decimal.ROUND_HALF_UP)


def decimal_capped(time, unit="ms"):
    gran = {
            'ns'  : '1.000000000',
            'us'  : '1.000000',
            'ms'  : '1.000',
            'sec' : '1.'
    }.get(unit)
    return time.quantize(decimal.Decimal(gran))


def seconds_stats(seconds):
    ''' return len(seconds), average, mean, min and max'''
    differences = []
    length = len(seconds)
    if length < 2:
        return 1, -1, -1, -1, -1
    for i in range(length - 1):
        prev = seconds[i]
        next = seconds[i+1]
        if (prev > next):
            # I dont see it, but triggered at differenz
            # CPU may result in quirk times, skip these just
            continue
        difference = next - prev
        differences.append(difference)
    if not differences:
        return None
    average = sum(differences) / len(differences)
    minimum = min(differences)
    maximum = max(differences)
    mean = statistics.mean(differences)
    return length, average, mean, minimum, maximum


def wakeups_per_second(no_wakeups):
    trace_runtime = event_time_last - event_time_first
    return decimal_capped(no_wakeups / trace_runtime, unit="ms")



def sched__sched_switch(event_name, context, common_cpu, common_secs, common_nsecs,
                        common_pid, common_comm, common_callchain, prev_comm,
                        prev_pid, prev_prio, prev_state, next_comm, next_pid,
                        next_prio, perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    next_comm = _filter_non_printable(next_comm)
    mode_cluster.sched__sched_switch(time, common_cpu, next_comm, next_pid, prev_pid, perf_sample_dict)
    mode_task.sched__sched_switch(time, common_cpu, next_comm, next_pid, prev_pid, perf_sample_dict)
    mode_frequency.sched__sched_switch(time, common_cpu, next_comm, next_pid, prev_pid, perf_sample_dict)
    mode_wakeups_timemap.sched__sched_switch(time, common_cpu, next_comm, next_pid, prev_pid, perf_sample_dict)


def irq__irq_handler_entry(event_name, context, common_cpu,
                           common_secs, common_nsecs, common_pid, common_comm,
                           common_callchain, irq, name, perf_sample_dict):

    time = time_convert(perf_sample_dict["sample"]["time"])
    mode_cluster.irq__irq_handler_entry(time, common_cpu, irq, name)
    mode_wakeups_timemap.irq__irq_handler_entry(time, common_cpu, irq, name)


def power__cpu_frequency(event_name, context, common_cpu, common_secs,
                         common_nsecs, common_pid, common_comm,
                         common_callchain, state, cpu_id, perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    mode_frequency.power__cpu_frequency(time, cpu_id, state)


def power__cpu_idle(event_name, context, common_cpu, common_secs, common_nsecs,
                    common_pid, common_comm, common_callchain, state, cpu_id, perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    mode_cluster.power__cpu_idle(time, cpu_id, state)
    mode_idle_governor.power__cpu_idle(time, cpu_id, state)


def power__cpu_idle_miss(event_name, context, common_cpu, common_secs,
        common_nsecs, common_pid, common_comm, common_callchain, cpu_id, state,
        below, perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    mode_cluster.power__cpu_idle_miss(time, common_cpu, state, below)
    mode_idle_governor.power__cpu_idle_miss(time, common_cpu, state, below)


def timer__hrtimer_init(event_name, context, common_cpu, common_secs,
        common_nsecs, common_pid, common_comm, common_callchain, hrtimer,
        clockid, mode, perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    clockid = symbol_str("timer__hrtimer_init", "clockid", clockid)
    mode = symbol_str("timer__hrtimer_init", "mode", mode)
    comm = _filter_non_printable(common_comm)
    mode_timer.timer__hrtimer_init(time, common_cpu, hrtimer, comm,
                                   common_pid, clockid, mode)


def timer__hrtimer_cancel(event_name, context, common_cpu, common_secs,
        common_nsecs, common_pid, common_comm, common_callchain, hrtimer,
        perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    mode_cluster.timer__hrtimer_cancel(time, common_cpu, hrtimer)
    mode_timer.timer__hrtimer_cancel(time, common_cpu, hrtimer)


def timer__timer_init(event_name, context, common_cpu, common_secs,
        common_nsecs, common_pid, common_comm, common_callchain, timer,
        perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    comm = _filter_non_printable(common_comm)
    mode_timer.timer__timer_init(time, common_cpu, timer, comm, common_pid)


def timer__timer_cancel(event_name, context, common_cpu, common_secs,
        common_nsecs, common_pid, common_comm, common_callchain, timer,
        perf_sample_dict):
    time = time_convert(perf_sample_dict["sample"]["time"])
    mode_timer.timer__timer_cancel(time, common_cpu, timer)


def trace_unhandled(event_name, context, event_fields_dict, perf_sample_dict):
    pass

def trace_begin():
    global ej, mode_timer, mode_cluster, mode_task
    global mode_frequency, mode_wakeups_timemap, mode_idle_governor
    args = parse_args()
    args_check_color(args)
    mode_timer = ModeTimer(args)
    mode_cluster = ModeCluster(args)
    mode_task = ModeTask(args)
    mode_frequency = ModeFrequency(args)
    mode_wakeups_timemap = ModeWakeupsTimemap(args)
    mode_idle_governor = ModeIdleGovernor(args)



def trace_end():
    mode_cluster.finalize()
    mode_timer.finalize()
    mode_task.finalize()
    mode_frequency.finalize()
    mode_wakeups_timemap.finalize()
    mode_idle_governor.finalize()


class Event(object):

    def __init__(self):
        self.title = "unknown"

class EventIdleMiss(Event):

    def __init__(self, time, cpu, state, below):
        self.title = "IdleMiss"
        self.time = time
        self.cpu = cpu
        self.state = state
        self.below = below

    def __str__(self):
        cpu_str = str_cpu_zeroized(self.cpu)
        return f"EventIdleMiss {cpu_str} [State: {self.state}, Below: {self.below}]"

    def str(self, fmt=None):
        if fmt == "cluster":
            return f'IdleMiss   {decimal_capped(self.time, unit="us")} [State: {self.state}, Below: {self.below}]'
        else:
            raise ValueError(f"fmt: {fmt} not supported")


class EventTimer(Event):

    def __init__(self, time, cpu, hrtimer):
        self.title = "Timer"
        self.time = time
        self.cpu = cpu
        self.hrtimer = hrtimer

    def __str__(self):
        cpu_str = str_cpu_zeroized(self.cpu)
        return f"EventTimer {cpu_str} [Name: {self.hrtimer}]"
    
    def str(self, fmt=None):
        if fmt == "cluster":
            return f'Timer      {decimal_capped(self.time, unit="us")} [Id: 0x{self.hrtimer:x}]'
        else:
            raise ValueError(f"fmt: {fmt} not supported")


class EventIrq(Event):

    def __init__(self, time, cpu, irq, name):
        self.title = "IRQ"
        self.time = time
        self.cpu = cpu
        self.irq = irq
        self.name = name

    def __str__(self):
        cpu_str = str_cpu_zeroized(self.cpu)
        return f"EventIrq  {cpu_str} [IRQ: {self.irq}, Name: {self.name}]"

    def str(self, fmt=None):
        if fmt == "cluster":
            return f'Interrupt  {decimal_capped(self.time, unit="us")} [Name: {self.name}, Irq: {self.irq}]'
        else:
            raise ValueError(f"fmt: {fmt} not supported")

class EventIdle(Event):

    def __init__(self, time, cpu, state):
        self.title = "Idle"
        self.time = time
        self.time_end = None
        self.cpu = cpu
        self.state = state

    def duration(self):
        return self.time_end - self.time

    def __str__(self):
        cpu_str = str_cpu_zeroized(self.cpu)
        return f"EventIdle {cpu_str} [State: {self.state}, CPU: {self.cpu}, Duration: {self.duration()}]"

class EventTask(Event):
    """ The class is used to handle the information of a given task."""

    def __init__(self, id, tid, cpu, comm, frequency=None):
        self.title = "Task"
        self.id = id
        self.tid = tid
        self.cpu = cpu
        self.comm = comm
        self.pid = None
        self._time_in = None
        self._time_out = None
        self.time = None # FIXME
        self.frequency = frequency

    def schedule_in_at(self, time):
        """set the time where the task was scheduled in"""
        self._time_in = time
        self.time = time

    def schedule_out_at(self, time):
        """set the time where the task was scheduled out"""
        self._time_out = time

    def update_pid(self, pid):
        self.pid = pid

    def __str__(self):
        cpu_str = str_cpu_zeroized(self.cpu)
        return f"EventTask {cpu_str} [Name: {self.comm}, PID: {self.pid}, Duration: {self._time_out - self._time_in}]"

    def duration(self):
        return decimal_to_ms_rounded(self._time_out - self._time_in)

    def str(self, fmt=None):
        duration_ms = decimal_to_ms_rounded(self._time_out - self._time_in)
        if fmt == "cluster":
            return f'Task       {decimal_capped(self._time_in, unit="us")} [Name: {self.comm}, PID: {self.pid}, TID: {self.tid}, Duration: {duration_ms} ms]'
        else:
            raise ValueError(f"fmt: {fmt} not supported")


class ModeTask(object):

    class TaskStats(object):

        def __init__(self, task):
            self.task = task
            self.wakeup_times = []
            self.threads = {}

        def wakeups(self):
            return len(self.wakeup_times)

        def thread_stats(self, task):
            if not task.tid in self.threads:
                self.threads[task.tid] = ModeTask.TaskStats(task)
            return self.threads[task.tid]

    def __init__(self, args):
        self.args = args
        self.task_running = {}
        self.task_stats = {}

    def activated(self):
        return True if self.args.mode in ("all", "task") else False

    def insert(self, task):
        if task.pid not in self.task_stats:
            self.task_stats[task.pid] = ModeTask.TaskStats(task=task)
        # overall process updates
        process_stat = self.task_stats[task.pid]
        process_stat.wakeup_times.append(task._time_in)

        # thread specific updates (if tid == pid -> thread leader)
        thread_stat = self.task_stats[task.pid].thread_stats(task)
        thread_stat.wakeup_times.append(task._time_in)

    def sched__sched_switch(self, time, cpu, next_comm, next_tid, prev_tid, perf_sample_dict):
        if not self.activated():
            return
        if next_tid == 0:
            # swapper/idle task is scheduled in
            _id = _task_id(prev_tid, cpu)
            if _id not in self.task_running:
                # may happen, if we missed the switch to
                # event. Seen in combination with --exclude-perf
                # where the start is filtered out, but not the
                # switched in. Probably a bug in exclude-perf
                # option.
                return
            task = self.task_running[_id]
            task.schedule_out_at(time)

            # record tid, during schedule in the tid
            # is not available, update now
            pid = int(perf_sample_dict["sample"]["pid"])
            task.update_pid(pid)
            self.insert(task)
            del self.task_running[_id]
        else:
            # a real task is switched in now, now do  bookkeeping for
            # this new task
            _id = _task_id(next_tid, cpu)
            if _id in self.task_running:
                # handle corner cases where already running tasks
                # are switched-to again - saw this via --exclude-perf
                # recorded traces. We simple ignore this "second start"
                # event.
                return
            task = EventTask(_id, next_tid, cpu, next_comm)
            task.schedule_in_at(time)
            self.task_running[_id] = task

    def info_by_process_task_stats(self, wakeup_times):
        wakeups, avg, mean, _min, _max = seconds_stats(wakeup_times)
        if wakeups > 1:
            mean = decimal_to_ms_rounded(mean)
            _min = decimal_to_ms_rounded(_min, quantize='0.000001')
            _max = decimal_to_ms_rounded(_max)
        wakeups_sec = wakeups_per_second(wakeups)
        return wakeups_sec, mean, _min, _max

    def info_by_process(self):
        processes = sorted(self.task_stats.values(), key=lambda p: p.wakeups(), reverse=True)
        for process in processes:
            wakeups_sec, mean_ms, min_ms, max_ms = self.info_by_process_task_stats(process.wakeup_times)
            print("{:<20} PID:{:>5} {:>10} {:>13} {:>11} {:>14} {:>11}".format(process.task.comm, process.task.pid, process.wakeups(),
                wakeups_sec, mean_ms, min_ms, max_ms))
            threads = sorted(process.threads.values(), key=lambda p: p.wakeups(), reverse=True)
            for thread in threads:
                thread_wakeups_sec, thread_mean_ms, thread_min_ms, thread_max_ms = self.info_by_process_task_stats(thread.wakeup_times)
                print("    {:<16} TID:{:>5} {:>10} {:>13} {:>11} {:>14} {:>11}".format(thread.task.comm, thread.task.tid, thread.wakeups(),
                    thread_wakeups_sec, thread_mean_ms, thread_min_ms, thread_max_ms))

    def finalize(self):
        if not self.activated():
            return
        self.info_by_process()


class ModeFrequency(object):

    def __init__(self, args):
        self.args = args
        self.task_running = {}
        self.idle_active = {}
        self.journal_cpu = {}
        self.frequency_cpu = {}
        self.journal = collections.deque()

    def frequency_current(self, cpu):
        return self.frequency_cpu.get(cpu, -1)

    def insert(self, cpu, event):
        if not cpu in self.journal_cpu:
            self.journal_cpu[cpu] = collections.deque()
        self.journal_cpu[cpu].append(event)
        self.journal.append(event)

    def journal_iter(self, cpu=None):
        """return a generator, if no cpu is given for global journal
        if given,the cpu specific generator queue"""
        if cpu is not None:
            for item in self.journal_cpu[cpu]:
                yield item
        else:
            for item in self.journal:
                yield item

    def activated(self):
        return True if self.args.mode in ("all", "frequency") else False

    def sched__sched_switch(self, time, cpu, next_comm, next_tid, prev_tid, perf_sample_dict):
        if not self.activated():
            return
        if next_tid == 0:
            # swapper/idle task is scheduled in
            _id = _task_id(prev_tid, cpu)
            if _id not in self.task_running:
                # may happen, if we missed the switch to
                # event. Seen in combination with --exclude-perf
                # where the start is filtered out, but not the
                # switched in. Probably a bug in exclude-perf
                # option.
                return
            task = self.task_running[_id]
            task.schedule_out_at(time)

            # record tid, during schedule in the tid
            # is not available, update now
            pid = int(perf_sample_dict["sample"]["pid"])
            task.update_pid(pid)
            self.insert(cpu, task)
            del self.task_running[_id]
        else:
            # a real task is switched in now, now do  bookkeeping for
            # this new task
            _id = _task_id(next_tid, cpu)
            if _id in self.task_running:
                # handle corner cases where already running tasks
                # are switched-to again - saw this via --exclude-perf
                # recorded traces. We simple ignore this "second start"
                # event.
                return
            frequency = self.frequency_cpu.get(cpu, -1)
            task = EventTask(_id, next_tid, cpu, next_comm, frequency=frequency)
            task.schedule_in_at(time)
            self.task_running[_id] = task

    def power__cpu_frequency(self, time, cpu_id, state):
        self.frequency_cpu[cpu_id] = state // 1000

    def show(self):
        fmt = csv_sep('{:>20}S{:>3}S{:>15}S{:>11}S{:>11}S{:>16}S{:>11}')
        print(fmt.format("Time", "CPU", "Frequency [MHz]", "PID",
                         "TID", "Comm", "Runtime [ms]"))
        for event in self.journal_iter(cpu=self.args.cpu):
            if not isinstance(event, EventTask):
                continue
            time_ns = decimal_capped(event.time, unit="ns")
            task_runtime = event.duration()
            msg = fmt.format(time_ns, event.cpu, event.frequency, event.pid,
                             event.tid, event.comm, task_runtime)
            print(csv_clean(msg))

    def finalize(self):
        if not self.activated():
            return
        self.show()


class ModeCluster(object):

    types = enum.Enum('Type', ['IDLE', 'TASK'])

    def __init__(self, args):
        self.args = args
        self.task_running = {}
        self.idle_active = {}
        self.journal_cpu = {}
        self.journal = collections.deque()

    def insert(self, cpu, event):
        if not cpu in self.journal_cpu:
            self.journal_cpu[cpu] = collections.deque()
        self.journal_cpu[cpu].append(event)
        # and global too, this is sorted chronological
        self.journal.append(event)

    def journal_gen(self, cpu=None):
        """return a generator, if no cpu is given for global journal
        if given,the cpu specific generator queue"""
        if cpu is not None:
            for item in self.journal_cpu[cpu]:
                yield item
        else:
            for item in self.journal:
                yield item

    def activated(self):
        return True if self.args.mode in ("all", "idle-cluster") else False

    def _power__cpu_idle_start(self, time, cpu, state):
        if cpu in self.idle_active:
            print("BUG")
            return
        idle = EventIdle(time, cpu, state)
        self.idle_active[cpu] = idle

    def _power__cpu_idle_end(self, time, cpu, state):
        if cpu not in self.idle_active:
            return
        idle = self.idle_active[cpu]
        idle.time_end = time

        self.insert(cpu, idle)
        del self.idle_active[cpu]

    def power__cpu_idle(self, time, cpu_id, state):
        if not self.activated():
            return
        if state == POWER_WAKE_ID:
            self._power__cpu_idle_end(time, cpu_id, state)
        else:
            self._power__cpu_idle_start(time, cpu_id, state)

    def irq__irq_handler_entry(self, time, cpu, irq, name):
        if not self.activated():
            return
        irq_event = EventIrq(time, cpu, irq, name)
        self.insert(cpu, irq_event)

    def timer__hrtimer_cancel(self, time, cpu, hrtimer):
        if not self.activated():
            return
        ev = EventTimer(time, cpu, hrtimer)
        self.insert(cpu, ev)

    def power__cpu_idle_miss(self, time, cpu, state, below):
        if not self.activated():
            return
        ev = EventIdleMiss(time, cpu, state, below)
        self.insert(cpu, ev)

    def sched__sched_switch(self, time, cpu, next_comm, next_tid, prev_tid, perf_sample_dict):
        if not self.activated():
            return
        if next_tid == 0:
            # swapper/idle task is scheduled in
            _id = _task_id(prev_tid, cpu)
            if _id not in self.task_running:
                # may happen, if we missed the switch to
                # event. Seen in combination with --exclude-perf
                # where the start is filtered out, but not the
                # switched in. Probably a bug in exclude-perf
                # option.
                return
            task = self.task_running[_id]
            task.schedule_out_at(time)

            # record tid, during schedule in the tid
            # is not available, update now
            pid = int(perf_sample_dict["sample"]["pid"])
            task.update_pid(pid)
            self.insert(cpu, task)
            del self.task_running[_id]
        else:
            # a real task is switched in now, now do  bookkeeping for
            # this new task
            _id = _task_id(next_tid, cpu)
            if _id in self.task_running:
                # handle corner cases where already running tasks
                # are switched-to again - saw this via --exclude-perf
                # recorded traces. We simple ignore this "second start"
                # event.
                return
            task = EventTask(_id, next_tid, cpu, next_comm)
            task.schedule_in_at(time)
            self.task_running[_id] = task

    def _value_to_ansi_color256_gradient(self, value, min_value, max_value):
        red_min, red_max = 0, 127
        green_min, green_max = 0, 255

        normalized_value = (value - min_value) / (max_value - min_value)

        red = int((1 - normalized_value) * red_max + normalized_value * red_min)
        green = int((1 - normalized_value) * green_min + normalized_value * green_max)

        ansi_code = 16 + (36 * int(red / 51)) + (6 * int(green / 51))
        return f'\033[48;5;{ansi_code}m'

    def decimal_to_ms_rounded(self, time):
        """ take Decimal in seconds, convert to ms and round to us granularity """
        ms = time * decimal.Decimal(1000.0)
        return ms.quantize(decimal.Decimal('0.001'), decimal.ROUND_HALF_UP)

    def _mode_all_print_idle_hdr(self, event, color):
        sleep_duration_ms = decimal_to_ms_rounded(event.duration())
        info_line = f"Wakeup at: {event.time_end} ms | Exit IdleState: {event.state} "
        color_line = f'{color}  {_COLORS_FG["black"]}{info_line}{_COLOR_RESET}'
        print(color_line)
        second_line = f'{color} {_COLOR_RESET}{_COLORS_FG["yellow"]} Idle interrupted after {sleep_duration_ms} ms{_COLOR_RESET}'
        print(f'{color}{second_line}{_COLOR_RESET}')

    def _mode_all_print_footer(self, color, event, idle_event_prev):
        active_duration = -1
        if idle_event_prev:
            active_time = event.time - idle_event_prev.time_end
            active_duration = decimal_to_ms_rounded(active_time)

        print(f'{color} {_COLOR_RESET}{_COLORS_FG["yellow"]} Duration of activity: {active_duration} ms - Going idle at FIXME{_COLOR_RESET}')

    def mode_cluster_print_event(self, event, line_prefix):
        idstr = event.str(fmt="cluster")
        print(f"{line_prefix}{idstr}")

    def output_per_cpu(self):
        ca = itertools.cycle([_COLORS_BG["purple"], _COLORS_BG["yellow"]])
        color = next(ca)
        line_prefix = f'{color} {_COLOR_RESET} '
        time_marker_prev = None
        idle_prev = None
        for event in self.journal_gen(cpu=self.args.cpu):
            self._mode_cluster_time_marker(event, time_marker_prev)
            if isinstance(event, EventIdle):
                self._mode_all_print_footer(color, event, idle_prev)
                color = next(ca)
                line_prefix = f'{color} {_COLOR_RESET} '
                self._mode_all_print_idle_hdr(event, color)
                idle_prev = event
            else:
                self.mode_cluster_print_event(event, line_prefix)


    def info_cpu_event(self, event, prev_db, fmt):
        if isinstance(event, EventIdle):
            return
        prev_was_idle, prev_idle_state, prev_idle_time = self.info_full_prev_idle(prev_db, event.cpu)
        is_wakeup = ""
        if prev_was_idle:
            is_wakeup = "*"
        msg = fmt.format(event.time, is_wakeup, prev_idle_time, prev_idle_state, event.title, event.str(fmt="cluster"))
        print(msg)

    def info_cpu(self):
        fmt = '{:>20} {:>20} {:>20} {:>20} {:>20} {:>20}' 
        prev_idle = None
        prev_db = dict()
        for event in self.journal_gen(cpu=self.args.cpu):
            self.info_cpu_event(event, prev_db, fmt)
            prev_db[event.cpu] = event


    def info_full_fmt(self):
        fmt = '{:>20} {:>20} {:>20} {:>20} {:>20}' 
        return fmt

    def info_full_prev_idle(self, prev_db, cpu):
        if cpu not in prev_db:
            return False, "", ""
        event = prev_db[cpu]
        if not isinstance(event, EventIdle):
            return False, "", ""
        return True, event.state, event.duration()

    def info_full(self):
        fmt = self.info_full_fmt()
        print(fmt.format("Time", "CPU", "Wakeup from", "Prev Idle Time[ms]", "Event"))
        prev_db = {}
        for event in self.journal_gen():
            prev_was_idle, prev_idle_state, prev_idle_time = self.info_full_prev_idle(prev_db, event.cpu)
            if not isinstance(event, EventIdle):
                print(fmt.format(event.time, event.cpu, prev_idle_state, prev_idle_time, event.str(fmt="cluster")))
                #print(fmt.format(event.cpu, event.time_in, prev_idle_state, prev_idle_time, "xxx"))#event.str(fmt="cluster")))
            prev_db[event.cpu] = event

    def finalize(self):
        if not self.activated():
            return
        if self.args.cpu is not None:
            #self.output_per_cpu()
            self.info_cpu()
        else:
            self.info_full()


class ModeTimer(object):

    types = enum.Enum('Type', ['HRTIMER', 'TIMER', 'UNKNOWN'])

    class Timer(object):
        """ Representation of one kernel timer """

        def __init__(self, timer_id, cpu, comm="unknown", tid=-1):
            self.id = timer_id
            self.cpu = cpu
            self.comm = comm
            self.tid = tid
            self.type = ModeTimer.types.UNKNOWN
            self.fired_log = []

        def fired(self, time, cpu):
            self.fired_log.append([time, cpu])

    def __init__(self, args):
        self.args = args
        self.timers_active = {}
        self.timers_tid = {}
        self.timers_cpu = {}
        self.timers_finished = []

    def activated(self):
        return True if self.args.mode in ("all", "timer") else False

    def update_tid_db(self, timer, cpu, time):
        """ a task (aka tid) may has multiple timers running
        we merge the info together here """
        if not timer.tid in self.timers_tid:
            db = {}
            db["fired"] = []
            db["comm"] = timer.comm
            db["tid"] = timer.tid
            db["cpu"] = dict()
            self.timers_tid[timer.tid] = db
        db = self.timers_tid[timer.tid]
        db["fired"].append(time)
        if cpu not in db["cpu"]:
            db["cpu"][cpu] = []
        db["cpu"][cpu].append(time)

    def update_cpu_db(self, cpu, time):
        if not cpu in self.timers_cpu:
            db = {}
            db["fired"] = []
            self.timers_cpu[cpu] = db
        db = self.timers_cpu[cpu]
        db["fired"].append(time)

    def timer__hrtimer_init(self, time, cpu, timer_id, comm, tid, clockid, mode):
        if not self.activated():
            return
        if timer_id in self.timers_active:
            timer = self.timers_active[timer_id]
            self.timers_finished.append(timer)
        timer = ModeTimer.Timer(timer_id, cpu, comm=comm, tid=tid)
        timer.type = ModeTimer.types.HRTIMER
        self.timers_active[timer_id] = timer

    def timer__hrtimer_cancel(self, time, cpu, timer_id):
        if not self.activated():
            return
        if not timer_id in self.timers_active:
            # timer was already running where perf was started,
            # no previous _init event for this cancel event
            timer = ModeTimer.Timer(timer_id, cpu)
            self.timers_active[timer_id] = timer
        timer = self.timers_active[timer_id]
        timer.fired(time, cpu)
        self.update_tid_db(timer, cpu, time)
        self.update_cpu_db(cpu, time)

    def timer__timer_init(self, time, cpu, timer_id, comm, tid):
        if not self.activated():
            return
        if timer_id in self.timers_active:
            timer = self.timers_active[timer_id]
            self.timers_finished.append(timer)
        timer = ModeTimer.Timer(timer_id, cpu, comm=comm, tid=tid)
        timer.type = ModeTimer.types.TIMER
        self.timers_active[timer_id] = timer

    def timer__timer_cancel(self, time, cpu, timer_id):
        if not self.activated():
            return
        if not timer_id in self.timers_active:
            # timer was already running where perf was started,
            # no previous _init event for this cancel event
            timer = ModeTimer.Timer(timer_id, cpu)
            self.timers_active[timer_id] = timer
        timer = self.timers_active[timer_id]
        timer.fired(time, cpu)
        self.update_tid_db(timer, cpu, time)
        self.update_cpu_db(cpu, time)

    def print_timer_info(self, timer, fmt):
        timer_id_hex = f'{timer.id:x}'
        timers = [i[0] for i in timer.fired_log]
        wakeups, avg, mean, _min, _max = seconds_stats(timers)
        mean_ms = decimal_to_ms_rounded(mean)
        min_ms = decimal_to_ms_rounded(_min, quantize='0.000001')
        max_ms = decimal_to_ms_rounded(_max)
        wakeups_sec = wakeups_per_second(wakeups)
        if wakeups <= 1:
            mean_ms, min_ms, max_ms = -1, -1, -1
        print(fmt.format(timer_id_hex, timer.type, timer.tid,
                         timer.comm, wakeups, wakeups_sec, mean_ms, min_ms, max_ms))

    def info_by_timer_sorted(self, timers, fmt):
        entries = sorted(timers, key=lambda x: len(x.fired_log), reverse=True)
        for timer in entries:
            self.print_timer_info(timer, fmt)

    def info_by_timer_fmt(self):
        fmt = "{:<16} {:<12} {:>5} {:>16} {:>11} {:>11}"
        if self.args.verbose:
            fmt = "{:<16} {:<12} {:>5} {:>16} {:>11} {:>13} {:>11} {:>14} {:>11}"
        return fmt

    def info_by_timer(self):
        fmt = self.info_by_timer_fmt()
        print(fmt.format("Timer ID", "Type", "TID", "Comm", "Triggered",
                         "Triggered/sec", "Mean [ms]", "Min [ms]", "Max [ms]"))
        self.info_by_timer_sorted(self.timers_active.values(), fmt)
        self.info_by_timer_sorted(self.timers_finished, fmt)

    def info_by_tid_cpu_fmt(self):
        fmt = "{:<16} {:>5} {:>11} {:>11} {:>11}"
        if self.args.verbose:
            fmt = "{:<16} {:>5} {:>11} {:>11} {:>11} {:>14} {:>11}"
        return fmt

    def info_by_tid_cpu(self):
        fmt = self.info_by_tid_cpu_fmt()
        print(fmt.format("Comm", "TID", "CPU", "Timers", "Timers/sec", "Mean [ms]", "Min [ms]", "Max [ms]"))
        entries = sorted(self.timers_tid.items(), key=lambda x: len(x[1]["fired"]), reverse=True)
        for entry in entries:
            tid, db = entry
            sorted_cpu_db = sorted(db["cpu"].keys())
            for cpu in sorted_cpu_db:
                if self.args.cpu is not None and cpu != self.args.cpu:
                    continue
                wakeups, avg, mean, _min, _max = seconds_stats(db["cpu"][cpu])
                mean_ms = decimal_to_ms_rounded(mean)
                min_ms = decimal_to_ms_rounded(_min, quantize='0.000001')
                max_ms = decimal_to_ms_rounded(_max)
                wakeups_sec = wakeups_per_second(wakeups)
                if wakeups <= 1:
                    mean_ms, min_ms, max_ms = -1, -1, -1
                print(fmt.format(db["comm"], tid, cpu, wakeups, wakeups_sec, mean_ms, min_ms, max_ms))

    def info_by_tid_fmt(self):
        fmt = '{:<16} {:>5} {:>11} {:>11}' 
        if self.args.verbose:
            fmt = "{:<16} {:>5} {:>11} {:>11} {:>11} {:>14} {:>11}"
        return fmt

    def info_by_tid(self):
        fmt = self.info_by_tid_fmt()
        print(fmt.format("Name", "TID", "Timers", "Timers/sec", "Mean [ms]", "Min [ms]", "Max [ms]"))
        entries = sorted(self.timers_tid.items(), key=lambda x: len(x[1]["fired"]), reverse=True)
        for entry in entries:
            tid, db = entry
            comm = db["comm"]
            wakeups, avg, mean, _min, _max = seconds_stats(db["fired"])
            mean_ms = decimal_to_ms_rounded(mean)
            min_ms = decimal_to_ms_rounded(_min, quantize='0.000001')
            max_ms = decimal_to_ms_rounded(_max)
            wakeups_s = wakeups_per_second(wakeups)
            if wakeups < 2:
                mean_ms, min_ms, max_ms = -1, -1, -1
            if self.args.verbose:
                m  = fmt.format(comm, tid, wakeups, wakeups_s, mean_ms, min_ms, max_ms)
            else:
                m  = fmt.format(comm, tid, wakeups, wakeups_s)
            print(m)

    def info_by_cpu_fmt(self):
        fmt = '{:>4} {:>11} {:>11}' 
        if self.args.verbose:
            fmt = "{:>4} {:>11} {:>11} {:>11} {:>14} {:>11}"
        return fmt

    def info_by_cpu(self):
        fmt = self.info_by_cpu_fmt()
        print(fmt.format("CPU", "Timers", "Timers/sec", "Mean [ms]", "Min [ms]", "Max [ms]"))
        entries = sorted(self.timers_cpu.items(), key=lambda x: len(x[1]["fired"]), reverse=True)
        for entry in entries:
            cpu, cpu_data = entry
            if self.args.cpu is not None and cpu != self.args.cpu:
                continue
            wakeups, avg, mean, _min, _max = seconds_stats(cpu_data["fired"])
            mean_ms = decimal_to_ms_rounded(mean)
            min_ms = decimal_to_ms_rounded(_min, quantize='0.000001')
            max_ms = decimal_to_ms_rounded(_max)
            wakeups_s = wakeups_per_second(wakeups)
            if wakeups < 2:
                mean_ms, min_ms, max_ms = -1, -1, -1
            print(fmt.format(cpu, wakeups, wakeups_s, mean_ms, min_ms, max_ms))

    def finalize(self):
        if not self.activated():
            return
        self.info_by_tid()
        print("")
        self.info_by_tid_cpu()
        print("")
        self.info_by_cpu()
        print("")
        self.info_by_timer()


class ModeWakeupsTimemap(object):


    class Task(object):

        def __init__(self, comm):
            self.comm = comm
            self.timestamps = []
            self.pid = -1


        def add_schedin(self, time):
            self.timestamps.append(time)



    def __init__(self, args):
        self.args = args
        self.task_db = {}
        self.task_cpu_db = {}
        self.irq_db = {}
        self.irq_cpu_db = {}


    def activated(self):
        return True if self.args.mode in ("all", "wakeups-timemap") else False


    def prologue(self, name):
        if not self.args.file_out:
            title = section_header(name)
            print(f"\n\n{title}\n")
            return sys.stdout
        fname = name.lower().replace(" ", "-") + ".txt"
        print(f"write data to {fname}")
        return open(fname, "w")


    def epilogue(self, fd):
        if not self.args.file_out:
            return
        fd.close()


    def create_linear_timemap(self, timestamps):
        wakeups = 0
        time_range = range(int(event_time_first), int(event_time_last) + 1)
        counter = collections.Counter({timestamp: 0 for timestamp in time_range})
        for timestamp in timestamps:
            d = {int(math.floor(timestamp)) : 1}
            counter.update(d)
            wakeups += 1
        wakeup_map = [counter[timestamp] for timestamp in time_range]
        return wakeups, wakeup_map, time_range


    def linear_wakeup_runner(self, iterable):
        for k, v in iterable.items():
            wakeups, wakeup_map, time_range = self.create_linear_timemap(v.timestamps)
            v.wakeups = wakeups
            v.wakeup_map = wakeup_map
        return time_range

    def finalize_task(self):
        fmt = "{:>7} {:>7} {:<16}"
        fmt_wakeups = " {:>6}"

        fd_out = self.prologue("Wakeups Timemap Task")
        time_range = self.linear_wakeup_runner(self.task_db)
        header = fmt.format("PID", "TID", "COMM")
        for timestamp in time_range:
            header += fmt_wakeups.format(timestamp)
        print(header, file=fd_out)

        task_db_sorted = sorted(self.task_db.items(), key=lambda x: x[1].wakeups, reverse=True)
        for tid, task in task_db_sorted:
            msg = fmt.format(task.pid, tid, task.comm.replace(" ", ""))
            for entry in task.wakeup_map:
                msg += fmt_wakeups.format(entry)
            print(msg, file=fd_out)
        self.epilogue(fd_out)


    def finalize_task_cpu(self):
        fmt = "{:>3}"
        fmt_wakeups = " {:>6}"

        fd_out = self.prologue("Wakeups Timemap Task CPU")
        time_range = self.linear_wakeup_runner(self.task_cpu_db)
        header = fmt.format("CPU")
        for timestamp in time_range:
            header += fmt_wakeups.format(timestamp)
        print(header, file=fd_out)

        cpu_db_sorted = sorted(self.task_cpu_db.items(), key=lambda x: x[0], reverse=False)
        for cpu, cpu_data in cpu_db_sorted:
            msg = fmt.format(cpu)
            for entry in cpu_data.wakeup_map:
                msg += fmt_wakeups.format(entry)
            print(msg, file=fd_out)


    def finalize_irq(self):
        fmt = "{:>4} {:>16}"
        fmt_wakeups = " {:>6}"

        fd_out = self.prologue("Wakeups Timemap IRQ")
        time_range = self.linear_wakeup_runner(self.irq_db)
        header = fmt.format("IRQ", "Name")
        for timestamp in time_range:
            header += fmt_wakeups.format(timestamp)
        print(header, file=fd_out)
        irq_db_sorted = sorted(self.irq_db.items(), key=lambda x: x[1].wakeups, reverse=True)
        for irq, irq_data in irq_db_sorted:
            msg = fmt.format(irq, irq_data.name.replace(" ", ""))
            for entry in irq_data.wakeup_map:
                msg += fmt_wakeups.format(entry)
            print(msg, file=fd_out)


    def finalize_irq_cpu(self):
        fmt = "{:>4} "
        fmt_wakeups = " {:>6}"

        fd_out = self.prologue("Wakeups Timemap IRQ CPU")
        time_range = self.linear_wakeup_runner(self.irq_cpu_db)
        header = fmt.format("CPU")
        for timestamp in time_range:
            header += fmt_wakeups.format(timestamp)
        print(header, file=fd_out)
        irq_cpu_db_sorted = sorted(self.irq_cpu_db.items(), key=lambda x: x[0], reverse=False)
        for cpu, cpu_data in irq_cpu_db_sorted:
            msg = fmt.format(cpu)
            for entry in cpu_data.wakeup_map:
                msg += fmt_wakeups.format(entry)
            print(msg, file=fd_out)


    def finalize(self):
        if not self.activated():
            return
        self.finalize_task()
        self.finalize_task_cpu()
        self.finalize_irq()
        self.finalize_irq_cpu()


    def is_cpu_filtered(self, cpu):
        if self.args.cpu is not None and cpu != self.args.cpu:
            return True
        return False


    def sched__sched_switch(self, time, cpu, next_comm, next_tid, prev_tid, perf_sample_dict):
        if not self.activated():
            return
        if self.is_cpu_filtered(cpu):
            return
        # perf task accounting
        if next_tid != 0:
            # a regular task/thread is scheduled in (!idle)
            if next_tid not in self.task_db:
                self.task_db[next_tid] = ModeWakeupsTimemap.Task(next_comm)
            task = self.task_db[next_tid]
            task.add_schedin(time)
        else:
            # swapper/idle task is scheduled in
            if prev_tid not in self.task_db:
                return
            # update PID, because TID is only available during sched-out
            self.task_db[prev_tid].pid = int(perf_sample_dict["sample"]["pid"])
        # perf cpu accounting
        if not cpu in self.task_cpu_db:
            self.task_cpu_db[cpu] = types.SimpleNamespace()
            self.task_cpu_db[cpu].timestamps = []
        self.task_cpu_db[cpu].timestamps.append(time)


    def irq__irq_handler_entry(self, time, cpu, irq, name):
        if not self.activated():
            return
        if self.is_cpu_filtered(cpu):
            return
        if not irq in self.irq_db:
            # IRQ DB
            self.irq_db[irq] = types.SimpleNamespace()
            self.irq_db[irq].name = name
            self.irq_db[irq].timestamps = []
        if not cpu in self.irq_cpu_db:
            self.irq_cpu_db[cpu] = types.SimpleNamespace()
            self.irq_cpu_db[cpu].timestamps = []

        self.irq_db[irq].timestamps.append(time)
        self.irq_cpu_db[cpu].timestamps.append(time)



class ModeIdleGovernor(object):

    class IdleEvent(object):

        def __init__(self, time, cpu, c_state):
            self.time = time
            self.cpu = cpu
            self.c_state = c_state
            self.c_state_name = None
            self.time_sleep = None
            self.time_delta = None
            self.miss = False
            self.below = None

        def update_end(self, time_end):
            self.time_sleep = int((time_end - self.time) * decimal.Decimal(1e9))

        def print_event(self, fd, fmt):
            # Can happen if the Core is still in an idle state, as described in  update_sysfs()
            if self.time_sleep is None:
                return
            event_msg = fmt.format(("{:.9f}".format(self.time) if self.time is not None else "-"), self.cpu,
                                   self.c_state_name, self.time_sleep, self.time_delta, self.miss,
                                   (self.below if self.below is not None else "-"))
            print(event_msg, file=fd)

        def update_miss(self, below):
            self.miss = True
            self.below = below

        def update_sysfs(self, c_state_db):
            residency = int(c_state_db[f"cpu{self.cpu}"][f"state{self.c_state}"]["residency"])
            # time_sleep can be unset if the c-state was not exited before record finished
            if self.time_sleep is not None:
                self.time_delta = self.time_sleep - (residency * 1000)
            self.c_state_name = c_state_db[f"cpu{self.cpu}"][f"state{self.c_state}"]["name"]


    def __init__(self, args):
        self.args = args
        self.db = []


    def activated(self):
        return self.args.mode in ("all", "idle-governor")


    def prologue(self, name, file_ext=".txt"):
        if not self.args.file_out:
            title = section_header(name)
            print(f"\n\n{title}\n")
            return sys.stdout
        fname = name.lower().replace(" ", "-") + file_ext
        print(f"write data to {fname}")
        return open(fname, "w")


    def epilogue(self, fd):
        if not self.args.file_out:
            return
        fd.close()


    def get_c_state_db(self):
        c_state_db = collections.defaultdict(dict)
        sys_path = "/sys/devices/system/cpu/"
        cpu_dirs = [d for d in os.listdir(sys_path) if re.match(r"^cpu\d+$", d)]

        for cpu_dir in sorted(cpu_dirs, key=lambda x: int(x[3:])):
            for state in sorted(os.listdir(sys_path + cpu_dir + "/cpuidle/")):
                c_state_db[cpu_dir][state] = {}
                c_state_path = sys_path + cpu_dir + "/cpuidle/" + state + "/"
                with open(c_state_path + "name", "r") as name_file, open(c_state_path + "residency", "r") as residency_file:
                    c_state_db[cpu_dir][state]["name"] = name_file.read().strip()
                    c_state_db[cpu_dir][state]["residency"] = residency_file.read().strip()
        c_state_db = dict(c_state_db)
        return c_state_db


    def print_idle_states(self):
        fd_out = self.prologue("Idle Governor Events")
        if len(self.db) == 0:
            return
        fmt = '{:>20} {:>5} {:>10} {:>14} {:>12} {:>6} {:>6}'
        print(fmt.format("Time-Start", "CPU", "C-State", "Sleep[ns]", "Delta[ns]", "Miss", "Below"), file=fd_out)
        for event in self.db:
            event.print_event(fd_out, fmt)
        self.epilogue(fd_out)

    def find_matching_event(self, cpu):
        # finds the last idle event for a cpu
        for event in self.db[::-1]:
            if event.cpu == cpu:
                return event
        return None


    def finalize(self):
        if not self.activated():
            return
        c_state_db = self.get_c_state_db()
        fd_out = self.prologue("C-State Idle Residency", file_ext=".json")
        print(json.dumps(c_state_db, indent=4), file=fd_out)
        self.epilogue(fd_out)
        # probably better to move delta calc to each event, such that there is no need for another iteration
        for event in self.db:
            event.update_sysfs(c_state_db)
        self.print_idle_states()


    def is_cpu_filtered(self, cpu):
        if self.args.cpu is not None and cpu != self.args.cpu:
            return True
        return False


    def power__cpu_idle_miss(self, time, cpu, state, below):
        if not self.activated() or self.is_cpu_filtered(cpu):
            return
        event = self.find_matching_event(cpu)
        if event is None:
            # can only occur then there is a miss as first or second trace of a CPU
            return
        event.update_miss(below)


    def power__cpu_idle(self, time, cpu, state):
        if not self.activated() or self.is_cpu_filtered(cpu):
            return
        if state != POWER_WAKE_ID:
            # go into idle state
            event = ModeIdleGovernor.IdleEvent(time, cpu, state)
            self.db.append(event)
        else:
            # transition into running state (-1)
            event = self.find_matching_event(cpu)
            if event is None:
                # can be None if a core already started in a c-state before record is called
                return
            event.update_end(time)
