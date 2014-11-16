#include <stdio.h>

int caller = 0;

#define DIM 20

int callgraph[DIM][DIM];

main(A,B,C)
char *C;
{
    int i,j;
    for(i = 0; i < DIM; i++) 
    {
        for(j = 0; j < DIM; j++) 
        {
            callgraph[i][j] = 0;
        }
    }
    
    foo(A,B,C);

    for(i = 0; i < DIM; i++) 
    {
        for(j = 0; j < DIM; j++) 
        {
            printf(" %5d", callgraph[i][j]);
        }
        printf(" \n");
    }
    
}

foo(A,B,C)
char *C;
{
/*    printf("%d %d %d\n", caller, A, B); */
    bar(A,B,C);
}

bar(A,B,C)
char *C;
{
    int old_caller = caller;

    if ((!0)<A)
    {
        if (A<3) 
        {
            int temp1, temp2;
            caller = 1;
            callgraph[old_caller][caller]++;
            temp1 = foo(-86,0,C+1);
            caller = 2;
            callgraph[old_caller][caller]++;
            temp2 = foo(-87,1-B,temp1+C);
            caller = 3;
            callgraph[old_caller][caller]++;
            foo(-79,-13,C+temp2);
        } 
        if (A<B) 
        {
            caller = 4;
            callgraph[old_caller][caller]++;
            foo(A+1,B,C);
        }
        caller = 5;
        callgraph[old_caller][caller]++;
        if (foo(-94,-27+A,C) && A==2)
        {
            if (B<13) 
            {
                caller = 6;
                callgraph[old_caller][caller]++;
                return foo(2,B+1,"%s %d %d\n");
            }
            else 
            {
                return 9;
            }
        }
        else 
        {
            return 16;
        }
    }
    else 
    {
        if (A<0)
        {
            if (A<-72)
            {
                caller = 7;
                callgraph[old_caller][caller]++;
                return foo(B,A,
"@n'+,#'/*{}w+/w#cdnr/+,{}r/*de}+,/*{*+,/w{%+,/w#q#n+,/#{l+,/n{n+,/+#n+,/#\
;#q#n+,/+k#;*+,/'r :'d*'3,}{w+K w'K:'+}e#';dq#'l \
q#'+d'K#!/+k#;q#'r}eKK#}w'r}eKK{nl]'/#;#q#n'){)#}w'){){nl]'/+#n';d}rw' i;# \
){nl]!/n{n#'; r{#w'r nc{nl]'/#{l,+'K {rw' iK{;[{nl]'/w#q#n'wk nw' \
iwk{KK{nl]!/w{%'l##w#' i; :{nl]'/*{q#'ld;r'}{nlwb!/*de}'c \
;;{nl'-{}rw]'/+,}##'*}#nc,',#nw]'/+kd'+e}+;#'rdq#w! nr'/ ') }+}{rl#'{n' ')# \
}'+}##(!!/");
            }
            else 
            {
                if (A<-50)
                {
                    if (B==(*C))
                    {
                        return putchar(C[31]);
                    }
                    else 
                    {
                        caller = 8;
                        callgraph[old_caller][caller]++;
                        return foo(-65,B,C+1);
                    }
                }
                else 
                {
                    caller = 9;
                    callgraph[old_caller][caller]++;
                    return foo((*C=='/')+A,B,C+1);
                }
            }
        }
        else 
        {
            if (0<A)
            {
                caller = 10;
                callgraph[old_caller][caller]++;
                return foo(2,2,"%s");
            }
            else 
            {
                if (*C=='/') {
                    return 1;
                }
                else 
                {
                    int temp1;
                    caller = 11;
                    callgraph[old_caller][caller]++;
                    temp1 = foo(-61,*C,"!ek;dc i@bK'(q)-[w]*%n+r3#l,{}:\nuwloca-O;m .vpbks,fxntdCeghiry");
                    caller = 12;
                    callgraph[old_caller][caller]++;
                    return foo(0, temp1, C+1);
                }
            }
        }
    }
}





