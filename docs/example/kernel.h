#pragma once

#include "machine.h"

typedef int i32;
typedef unsigned int u32;
typedef long long i64;
typedef unsigned long long u64;

enum Kernel_proc_status {
  Kernel_READY,
  Kernel_RUNNING,
};

struct Kernel_proc {
  unsigned long long pid;
  unsigned long long regs[32];
  enum Kernel_proc_status status;
};

struct Kernel_state {
  unsigned long long curr_pid;
  struct Kernel_proc procs[5];
  unsigned long long deadline;
  struct Machine_state *mc;
};

extern unsigned long long const Kernel_nb_procs;

extern unsigned long long const Kernel_quantum;

extern unsigned long long const Kernel_nb_procs;

extern unsigned long long const Kernel_quantum;

struct Kernel_state *Kernel_schedule(struct Kernel_state *, unsigned long long);


