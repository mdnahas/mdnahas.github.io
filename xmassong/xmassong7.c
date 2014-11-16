#include <stdio.h>

int caller = 0;
#define DIM 20
int callgraph[DIM][DIM];


main(A,B,C)
char *C;
{
    foo10(A,B,C);
}


foo10(A,B,C)
char *C;
{
    return foo(2,2,"%s");
}


/* Substitution function!  (see call to foo8) */
foo8(A,B,C)
char *C;
{
    while (B != (*C)) 
        C++;

    return putchar(C[31]);
    
/*  Calls 8 and 15.
    if (B==(*C))
    {
        return putchar(C[31]);
    }
    else 
    {
        return foo8(-65,B,C+1);
    }
    */
}



foo7(A,B,C)
char *C;
{
    {
        if (A<0)
        {
            if (A<-72)
            {
                caller = 7;
                return foo7(B,A,
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
                    caller = 9;
                    return foo7((*C=='/')+A,B,C+1);
            }
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
                    temp1 = foo8(-61,*C,"!ek;dc i@bK'(q)-[w]*%n+r3#l,{}:\nuwloca-O;m .vpbks,fxntdCeghiry");
                    caller = 12;
                    return foo7(0, temp1, C+1);
                }
        }
    }
}





foo(A,B,C)
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
            temp1 = foo7(-86,0,C+1);
            caller = 2;
            callgraph[old_caller][caller]++;
            temp2 = foo7(-87,1-B,temp1+C);
            caller = 3;
            callgraph[old_caller][caller]++;
            foo7(-79,-13,C+temp2);
        } 
        if (A<B) 
        {
            caller = 4;
            callgraph[old_caller][caller]++;
            foo(A+1,B,C);
        }
        caller = 5;
        callgraph[old_caller][caller]++;
        if (foo7(-94,-27+A,C) && A==2)
        {
            if (B<13) 
            {
                caller = 6;
                callgraph[old_caller][caller]++;
                return foo(2,B+1,"%s %d %d\n");
            }
            else 
            {
                callgraph[old_caller][13]++;
                return 9;
            }
        }
        else 
        {
            callgraph[old_caller][14]++;
            return 16;
        }
    }
}





