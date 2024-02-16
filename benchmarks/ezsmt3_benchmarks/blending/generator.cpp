#include <cstdio>
#include <cstdlib>
#include <time.h>

#define SUBS 15                 // number of substances
#define COMP 3                  // number of components

int main() {
    int temp;
    srand(time(NULL));
    printf("subs(1..%d).\n",SUBS);
    for (int i=1;i<=SUBS;i++) {
        temp=30+rand()%31;      // cost of each component 30-60
        printf("cost(%d,%d).\n",i,temp);
    }
    printf("comp(1..%d).\n",COMP);
    for (int i=1;i<=COMP;i++) {
        temp=50+rand()%251;     // required quantity of each component 50-300
        printf("mi(%d,%d).\n",i,temp);
    }
    for (int i=1;i<=SUBS;i++) {
        for (int j=1;j<=COMP;j++) {
            temp=50+rand()%250; // quantity of each component in each substance 50-300
            printf("tab(%d,%d,%d). ",i,j,temp);
        }
        printf("\n");
    }
    temp=65+rand()%11;          // budget 65-75
    printf("max_money(%d).\n",temp);
    temp=1+rand()%3;            // using cost 1-3
    printf("using_cost(%d).\n",temp);

    printf("not_together(1,2).\n");

    printf("have_to_use(3,1,4).\n");

    return 0;
}
