#include "machine.h"

struct Kernel_proc;
struct Kernel_state;
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

extern unsigned long long Machine_read_time(struct Machine_state *);
extern struct Machine_state *Machine_write_timecmp(struct Machine_state *, unsigned long long);
struct Kernel_state *Kernel_sync(struct Kernel_state *);
struct Kernel_state *Kernel_schedule(struct Kernel_state *);
unsigned long long const Kernel_NB_PROCS = 5LL;

unsigned long long const Kernel_QUANTUM = 100LL;

struct Kernel_state *Kernel_sync(struct Kernel_state *$p_ks)
{
  register struct Machine_state *$b1;
  register unsigned long long $b2;
  register struct Machine_state *$b0;
  register struct Kernel_state *$i0;
  $b1 = (*$p_ks).mc;
  $b2 = (*$p_ks).deadline;
  $b0 = Machine_write_timecmp($b1, $b2);
  (*$p_ks).mc = $b0;
  $i0 = $p_ks;
  return $i0;
}

struct Kernel_state *Kernel_schedule(struct Kernel_state *$p_ks)
{
  register struct Machine_state *$b8;
  register unsigned long long $b7;
  register unsigned long long $b9;
  register _Bool $b6;
  register unsigned long long $b1;
  register unsigned long long $b0;
  register unsigned long long $u_next_pid;
  register unsigned long long $b3;
  register unsigned long long $b2;
  register unsigned long long $b5;
  register unsigned long long $b4;
  register struct Kernel_proc *$u_proc;
  register struct Kernel_proc **$u_procs;
  register struct Kernel_state *$u_ks;
  register struct Kernel_state *$i0;
  $b8 = (*$p_ks).mc;
  $b7 = Machine_read_time($b8);
  $b9 = (*$p_ks).deadline;
  $b6 = $b7 > $b9;
  if ($b6) {
    $b1 = (*$p_ks).curr_pid;
    $b0 = $b1 + 1LL;
    $u_next_pid = $b0 % Kernel_NB_PROCS;
    (*$p_ks).curr_pid = $u_next_pid;
    $u_ks = $p_ks;
    $b3 = (*$u_ks).deadline;
    $b2 = $b3 + Kernel_QUANTUM;
    (*$u_ks).deadline = $b2;
    $u_ks = $u_ks;
    $u_procs = (*$u_ks).procs;
    $u_proc = *($u_procs + $u_next_pid);
    $b5 = (*$u_proc).nb_sched;
    $b4 = $b5 + 1LL;
    (*$u_proc).nb_sched = $b4;
    $u_proc = $u_proc;
    *($u_procs + $u_next_pid) = $u_proc;
    $u_procs = $u_procs;
    (*$u_ks).procs = $u_procs;
    $u_ks = $u_ks;
    $i0 = Kernel_sync($u_ks);
    return $i0;
  } else {
    return $p_ks;
  }
}


