#pragma once

#include "machine.h"

typedef int i32;
typedef unsigned int u32;
typedef long long i64;
typedef unsigned long long u64;

struct Kernel_proc {
  unsigned long long pid;
  unsigned long long *regs;
  unsigned long long nb_sched;
};

struct Kernel_state {
  unsigned long long curr_pid;
  struct Kernel_proc **procs;
  unsigned long long deadline;
  struct Machine_state *mc;
};

extern unsigned long long const Kernel_nb_procs;

extern unsigned long long const Kernel_quantum;

extern unsigned long long Machine_read_time(struct Machine_state *);
extern struct Machine_state *Machine_write_timecmp(struct Machine_state *, unsigned long long);
struct Kernel_state *Kernel_sync(struct Kernel_state *);
struct Kernel_state *Kernel_incr_proc_nb_sched(struct Kernel_state *, unsigned long long);
struct Kernel_state *Kernel_schedule(struct Kernel_state *);

