#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "proc.h"
#include "syscall.h"

int main()
{
    int fd = open("README", O_RDWR);
    char* text = (char*)mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_POPULATE, fd, 1);
    
    printf(1,"freemem is %d\n",freemem());
    printf(1, "return addr is %d\n", text);
    printf(1, "text[0] is: %c\n", text[0]);

    int child;
    if((child = fork()) != 0) {
        wait();
        printf(1, "fork: parent freemem is %d\n",freemem());
        printf(1, "parent: text[3] is: %c\n", text[3]);
    }

    else{
        printf(1, "fork: child freemem is %d\n",freemem());
        printf(1, "child: text[2] is: %c\n", text[2]);
    }

    exit();
}