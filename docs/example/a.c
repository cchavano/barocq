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

extern unsigned long long Machine_read_time(struct Machine_state *);
extern struct Machine_state *Machine_write_timecmp(struct Machine_state *, unsigned long long);
struct Kernel_state *Kernel_sync(struct Kernel_state *);
struct Kernel_state *Kernel_update_proc_status(struct Kernel_state *, unsigned long long, enum Kernel_proc_status);
struct Kernel_state *Kernel_schedule(struct Kernel_state *);
unsigned long long const Kernel_nb_procs = 5LL;

unsigned long long const Kernel_quantum = 100LL;

struct Kernel_state *Kernel_sync(struct Kernel_state *$p_ks)
{
  register struct Machine_state *$b0;
  register unsigned long long $b1;
  register struct Machine_state *$b2;
  register struct Kernel_state *$i0;
  $b0 = (*$p_ks).mc;
  $b1 = (*$p_ks).deadline;
  $b2 = Machine_write_timecmp($b0, $b1);
  $i0 = $p_ks;
  return $i0;
}

struct Kernel_state *Kernel_update_proc_status(struct Kernel_state *$p_ks, unsigned long long $p_pid, enum Kernel_proc_status $p_status)
{
  register struct Kernel_proc *$u_procs;
  register struct Kernel_proc *$u_proc;
  register struct Kernel_state *$i0;
  $u_procs = (*$p_ks).procs;
  $u_proc = &*($u_procs + $p_pid);
  (*$u_proc).status = $p_status;
  $i0 = $p_ks;
  return $i0;
}

struct Kernel_state *Kernel_schedule(struct Kernel_state *$p_ks)
{
  register struct Machine_state *$b0;
  register unsigned long long $b1;
  register unsigned long long $b2;
  register unsigned long long $u_curr_pid;
  register unsigned long long $u_next_pid;
  register unsigned long long $b3;
  register unsigned long long $u_next_deadline;
  register struct Kernel_state *$b4;
  register struct Kernel_state *$u_ks;
  register struct Kernel_state *$i0;
  $b0 = (*$p_ks).mc;
  $b1 = Machine_read_time($b0);
  $b2 = (*$p_ks).deadline;
  if ($b1 > $b2) {
    $u_curr_pid = (*$p_ks).curr_pid;
    $u_next_pid = ($u_curr_pid + 1LL) % Kernel_nb_procs;
    $b3 = (*$p_ks).deadline;
    $u_next_deadline = $b3 + Kernel_quantum;
    $u_ks = Kernel_update_proc_status($p_ks, $u_curr_pid, Kernel_READY);
    $u_ks = Kernel_update_proc_status($u_ks, $u_next_pid, Kernel_RUNNING);
    (*$u_ks).curr_pid = $u_next_pid;
    $b4 = $u_ks;
    (*$b4).deadline = $u_next_deadline;
    $u_ks = $b4;
    $i0 = Kernel_sync($u_ks);
    return $i0;
  } else {
    return $p_ks;
  }
}


