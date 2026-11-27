from math import prod
from pathlib import Path
from subprocess import check_output,run
from tempfile import TemporaryDirectory
from density import maximize


def check():
    ncases=0
    paths=0
    with TemporaryDirectory() as temp:
        binary=temp+'/brute'
        run(['c++','-std=c++17','-O3',str(Path(__file__).with_name('brute_density.cpp')),'-o',binary],check=True)
        for chain,q in [([1,2,4,8],3),([1,2,4,8],5),([1,2,4],9),([1,3,6],5),
                         ([1,3,9],2),([1,2,6,12],5),([1,5,10],3)]:
            N=q*chain[-1]
            mods=chain[1:]+[q*x for x in chain]
            optimum=list(map(int,check_output([binary,str(N),*map(str,mods)]).split()))
            for subset,n in enumerate(optimum):
                I=[i for i in range(1,len(chain)) if subset & (1<<(i-1))]
                J=[i for i in range(len(chain)) if subset & (1<<(len(chain)-1+i))]
                ratio,R=maximize(chain,q,I,J)
                assert ratio*N==n
                assert sum(any(x%m==r for m,r in R.items()) for x in range(N))==n
            ncases+=len(optimum)
            paths+=prod(m+1 for m in mods)
            print(chain,q,len(optimum),"subsets",flush=True)
    print(ncases,"optima and witness tuples verified;",paths,"residue assignments including omissions.")
if __name__=='__main__':check()
