#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

struct mmap_area ma[64] = { 0 };

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  for (int i = 0; i < 64; i++) {
    if (ma[i].p == curproc && ma[i].present == 1) {
      for (int j = 0; j < 64; j++) {
        if (ma[j].present == 0) {
          if (ma[i].f != 0) {
            ma[j].f = ma[i].f;
            filedup(ma[j].f);
            ma[j].f->off = ma[i].offset;  
          }
          ma[j].addr = ma[i].addr;
          ma[j].flags = ma[i].flags;
          ma[j].length = ma[i].length;
          ma[j].p = np;
          ma[j].present = 1;
          ma[j].prot = ma[i].prot;
          ma[j].offset = ma[i].offset;

          pte_t *pte;
          uint flags;
          uint ptr = 0;
          char *mem;

          for(ptr = ma[j].addr; ptr < ma[j].addr + ma[j].length; ptr += PGSIZE) {
            if((pte = walkpgdir(curproc->pgdir, (void *)ptr, 0)) == 0) {
              // cprintf("fork: pte should exist\n");
              return -1;
            }
              
            if(!(*pte & PTE_P)) {
              // cprintf("fork: page not present\n");
              return -1;
            }

            flags = PTE_FLAGS(*pte);
            if((mem = kalloc()) == 0) {
              // cprintf("fork: kalloc failed");
              return -1;
            }

            memset((void *)mem, 0, PGSIZE);

            memmove(mem, (void *)ptr, PGSIZE);

            if(mappages(np->pgdir, (void*)ptr, PGSIZE, V2P(mem), flags) < 0) {
              // cprintf("fork: mappages failed");
              return -1;
            }
          }

          break;
        }
      }
    }
  }

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE)
        continue;

      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
    }
    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

uint
mmap(uint addr, int length, int prot, int flags, int fd, int offset) {

  struct proc *p = myproc();
  struct file *f = 0;
  if (fd != -1)
    f = p->ofile[fd];

  int read = 0;
  int write = 0;

  if (prot & PROT_READ)
    read = 1;
  if (prot & PROT_WRITE)
    write = 1;

  int anonymous = 0;
  int populate = 0;

  if (flags & MAP_ANONYMOUS)
    anonymous = 1;
  if (flags & MAP_POPULATE)
    populate = 1;

  if (anonymous == 0 && fd == -1) {
    // cprintf("It's not anonymous, but when the fd is -1\n");
    return 0;
  }
  if (f != 0 && (read != f->readable || write != f->writable)) {
    // cprintf("The protection of the file and the prot of the parameter are different\n");
    return 0;
  }

  int i = 0;
  for (i = 0; (ma[i].present != 0) && i < 64; i++);
  if (i == 64) {
    // cprintf("There are no empty space in mmap_area\n");
    return 0;
  }

  uint start_addr = MMAPBASE + addr;
  
  if (f != 0) {
    filedup(f);
    ma[i].f = f;
  }
  ma[i].addr = start_addr;
  ma[i].flags = flags;
  ma[i].length = length;
  ma[i].prot = prot;
  ma[i].p = p;
  ma[i].offset = offset;
  ma[i].present = 1;

  if (populate == 0) {
    // cprintf("just record its mapping area\n");
    return start_addr;
  }

  if (populate == 1) {
    if (anonymous == 0) { // file mapping
      f->off = offset;
      uint ptr = 0; 
      char *new_physical_page = 0;

      for (ptr = start_addr; ptr < start_addr + length; ptr += PGSIZE) {
        new_physical_page = kalloc();
        if (new_physical_page == 0) {
          // cprintf("Failed to allocate physical page in file mapping\n");
          return 0;
        }

        memset(new_physical_page, 0, PGSIZE);
        fileread(f, new_physical_page, PGSIZE);

        if (mappages(p->pgdir, (void *)ptr, PGSIZE, V2P(new_physical_page), prot | PTE_U) == -1) {
          // cprintf("Failed to mappages in file mapping\n");
          return 0;
        }
          
      }

      return start_addr;
    }

    else if (anonymous == 1) { // anonymous mapping
      uint ptr = 0; 
      char *new_physical_page = 0;

      for (ptr = start_addr; ptr < start_addr + length; ptr += PGSIZE) {
        new_physical_page = kalloc();
        if (new_physical_page == 0) {
          // cprintf("Failed to allocate physical page in anonymous mapping\n");
          return 0;
        }

        memset(new_physical_page, 0, PGSIZE);

        if (mappages(p->pgdir, (void *)ptr, PGSIZE, V2P(new_physical_page), prot | PTE_U) == -1) {
          // cprintf("Failed to mappages in anonymous mapping\n");
          return 0;
        } 
      }

      return start_addr;
    }
  }
  
  return start_addr;
}

int
pfh(uint addr, uint err) {
  struct proc *p = myproc();
  
  int read = 0;
  int write = 0;
  if ((err&2) == 0)
    read = PROT_READ;
  if ((err&2) == 2)
    write = PROT_WRITE;

  int ma_idx = -1;

  for (int i = 0; i < 64; i++) {
    if ((ma[i].addr <= addr) && (addr <= (ma[i].addr + ma[i].length))) {
      if (ma[i].present == 1 && ma[i].p == p) {
        ma_idx = i;
        break;
      }
    }
  }

  if (ma_idx == -1) {
    // cprintf("Corresponding mmap_area is not found\n");
    return -1;
  }

  if (((ma[ma_idx].prot & PROT_READ) != read) || ((ma[ma_idx].prot & PROT_WRITE) != write)) {
    // cprintf("tf->err and prot in mmap_area is not same\n");
    return -1;
  }

  int anonymous = 0;
  if (ma[ma_idx].flags & MAP_ANONYMOUS)
    anonymous = 1;

  if (anonymous == 0) { // file mapping
      struct file *f = ma[ma_idx].f;
      f->off = ma[ma_idx].offset;
      uint ptr = 0; 
      char *new_physical_page = 0;

      for (ptr = ma[ma_idx].addr; ptr < ma[ma_idx].addr + ma[ma_idx].length; ptr += PGSIZE) {
        new_physical_page = kalloc();
        if (new_physical_page == 0) {
          // cprintf("Failed to allocate physical page in file mapping\n");
          return -1;
        }

        memset(new_physical_page, 0, PGSIZE);
        fileread(f, new_physical_page, PGSIZE);

        if (mappages(p->pgdir, (void *)ptr, PGSIZE, V2P(new_physical_page), ma[ma_idx].prot | PTE_U) == -1) {
          // cprintf("Failed to mappages in file mapping\n");
          return -1;
        }
          
      }

      return 0;
    }

    else if (anonymous == 1) { // anonymous mapping
      uint ptr = 0; 
      char *new_physical_page = 0;

      for (ptr = ma[ma_idx].addr; ptr < ma[ma_idx].addr + ma[ma_idx].length; ptr += PGSIZE) {
        new_physical_page = kalloc();
        if (new_physical_page == 0) {
          // cprintf("Failed to allocate physical page in anonymous mapping\n");
          return -1;
        }

        memset(new_physical_page, 0, PGSIZE);

        if (mappages(p->pgdir, (void *)ptr, PGSIZE, V2P(new_physical_page), ma[ma_idx].prot | PTE_U) == -1) {
          // cprintf("Failed to mappages in anonymous mapping\n");
          return -1;
        } 
      }

      return 0;
    }

    return 0;
}

int
munmap(uint addr) {
  struct proc *p = myproc();
  int ma_idx = -1;

  for (int i = 0; i < 64; i++) {
    if (ma[i].addr == addr) {
      if (ma[i].present == 1 && ma[i].p == p) {
        ma_idx = i;
        break;
      }
    }
  }

  if (ma_idx == -1) {
    // cprintf("Corresponding mmap_area is not found\n");
    return -1;
  }

  pte_t *TBF_page = 0;
  uint ptr = 0;

  for (ptr = ma[ma_idx].addr; ptr < ma[ma_idx].addr + ma[ma_idx].length; ptr += PGSIZE) {
    TBF_page = walkpgdir(p->pgdir, (void *)ptr, 0);
      if (TBF_page == 0) {
        // cprintf("To Be Free Page is not found by walkpdgir");
        continue;
      }
      if ((*TBF_page & PTE_P) == 0) {
        // cprintf("TBF_page is not physically allocated");
        continue;
      }
    uint pa = PTE_ADDR(*TBF_page);
    char *v = P2V(pa);
    memset((void *)v, 1, PGSIZE);
    kfree(v);

    *TBF_page = 0;
  }

  ma[ma_idx].f = 0;
  ma[ma_idx].addr = 0;
  ma[ma_idx].length = 0;
  ma[ma_idx].offset = 0;
  ma[ma_idx].prot = 0;
  ma[ma_idx].flags = 0;
  ma[ma_idx].p = 0;
  ma[ma_idx].present = 0;

  return 1;
}

int freemem(void) {
  return getFree();
}