#include "machine.h"

struct Kernel_proc;
struct Kernel_state;
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

static struct Kernel_state *Kernel_update_proc_status(struct Kernel_state *, unsigned long long, enum Kernel_proc_status);

struct Kernel_state *Kernel_schedule(struct Kernel_state *, unsigned long long);

extern struct Machine_state *Machine_write_timecmp(struct Machine_state *, unsigned long long);

unsigned long long const Kernel_nb_procs = 5LL;

unsigned long long const Kernel_quantum = 100LL;

static inline struct Kernel_state *Kernel_update_proc_status(struct Kernel_state *p_ks, unsigned long long p_pid, enum Kernel_proc_status p_status)
{
  struct Kernel_proc *u1_procs;
  struct Kernel_proc *u1_proc;
  struct Kernel_proc *u2_proc;
  struct Kernel_proc *u2_procs;
  struct Kernel_state *res;
  u1_procs = (*p_ks).procs;
  u1_proc = u1_procs + p_pid;
  (*u1_proc).status = p_status;
  u2_proc = u1_proc;
  u2_procs = u1_procs;
  res = p_ks;
  return res;
}

struct Kernel_state *Kernel_schedule(struct Kernel_state *p_ks, unsigned long long p_now)
{
  unsigned long long u1_curr_pid;
  unsigned long long u1_next_pid;
  unsigned long long u1_next_deadline;
  struct Kernel_state *u1_ks;
  struct Kernel_state *u2_ks;
  struct Kernel_state *b2;
  struct Kernel_state *u3_ks;
  struct Machine_state *b5;
  struct Kernel_state *res;
  if (p_now > (*p_ks).deadline) {
    u1_curr_pid = (*p_ks).curr_pid;
    u1_next_pid = (u1_curr_pid + 1LLU) % Kernel_nb_procs;
    u1_next_deadline = p_now + Kernel_quantum;
    u1_ks = Kernel_update_proc_status(p_ks, u1_curr_pid, Kernel_READY);
    u2_ks = Kernel_update_proc_status(u1_ks, u1_next_pid, Kernel_RUNNING);
    (*u2_ks).curr_pid = u1_next_pid;
    b2 = u2_ks;
    (*b2).deadline = u1_next_deadline;
    u3_ks = b2;
    b5 = Machine_write_timecmp((*u3_ks).mc, (*u3_ks).deadline);
    res = u3_ks;
    return res;
  } else {
    return p_ks;
  }
}


