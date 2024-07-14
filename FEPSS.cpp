#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <vector>
#include <math.h>
#include <assert.h>
#include <algorithm>
#include <ilcplex/ilocplex.h>
using namespace std;

typedef struct{
	int *X;
	int *S;
	int *NS;
	int IN, ON;
	int *IW;
	long int f;
} Solution;
typedef struct Neighbor{
	int f; 
    int type;
    int IO; 
    int k; 
    int x;
    int x1;
    int y1; 
} Neighbor;

string File_Name;

int *W1, *W2, *W3;
int *H1, *H2, *H3;
int *P1, *P, *B;
int **R, **R1, **M_R;
int *iterator_time, *G_BEST_history;
int *NeedSearchIndex, *DidtNeedSearchIndex, *ReSearchList;
int *order;
int *status;

double *Weight, *Weight2;
double *PR;
double *dataNM, *dataM;

long int L;

int K;
int seeds;
int N, M;
int f, f_best;
int tmax, cplex_tamx;
int SolutionState;

double BestResult;
double time_to_target, CutTime;
double time_one_run, starting_time, sec_starting_time;

int redo=0;
int history_offset = 0;
int status_index = 0;
int IterMax = 500;
int Maxnumber = 100000;
double EXACT_T = 0;
const int NeedNumber = 100;

Solution SC;
Solution SCbest;
Solution S_BEST;
Solution G_BEST; 
Solution SAVE_SOLUTIONS[NeedNumber+1];
// tool functions
void q_sort(double numbers[], int left, int right, int index[])
{
  int pivot, pivot_index, l_hold, r_hold;
  l_hold = left;
  r_hold = right;
  pivot = numbers[left];
  pivot_index = index[left] ;
  while (left < right)
  {
    while ((numbers[right] >= pivot) && (left < right))
      right--;
    if (left != right)
    {
      numbers[left] = numbers[right];
      index[left] = index[right];
      left++;
    }
    while ((numbers[left] <= pivot) && (left < right))
      left++;
    if (left != right)
    {
      numbers[right] = numbers[left];
      index[right] = index[left];
      right--;
    }
  }
  numbers[left] = pivot;
  index[left] = pivot_index;
  pivot = left;
  left = l_hold;
  right = r_hold;
  if (left < pivot)
    q_sort(numbers, left, pivot-1, index);
  if (right > pivot)
    q_sort(numbers, pivot+1, right, index);
}

void quick_sort(double numbers[], int array_size, int index[])
{
  q_sort(numbers, 0, array_size - 1, index);
}

void copy_sc(Solution SA, Solution &SB)
{
    int i,j;
    for(i=0;i<N;i++) {
        SB.X[i] = SA.X[i];
    }
    for(i=0;i<M;i++) {
        SB.IW[i] = SA.IW[i];
    }
    for(i=0; i<SA.IN; i++) {
        SB.S[i] = SA.S[i];
    }
    for(i=0; i<SA.ON; i++) {
        SB.NS[i] = SA.NS[i];
    }
    SB.IN=SA.IN;
    SB.ON=SA.ON;
    SB.f=SA.f;
}

void proof(Solution &S)
{
   int i,j;
   int count,p;
   printf("\n %ld \n",S.f) ;

   for(i=0;i<N;i++) printf("%d ",S.X[i]); printf("\n");
   for(i=0;i<M;i++) S.IW[i] = 0;
   for(i=0;i<M;i++)
   for(j=0;j<N;j++)
   S.IW[i] += S.X[j]*R[i][j];
   for(i=0;i<M;i++)
   {
      if(S.IW[i]>B[i]) printf("errer !") ;
   }
   printf("\n");
   count = 0;
   p=0;
   for(i=0;i<N;i++) if(S.X[i]==1) count++;
   for(i=0;i<N;i++) if(S.X[i]==1) p+=P[i];
   S.f = p;
   printf("count = %d   p=%d \n",count,p);
}

int hamming_distance(Solution SA, Solution SB)
{
    int i,dis;
    dis=0;
    for(i=0;i<N;i++) {
        if (SA.X[i]!=SB.X[i]) dis++;
    }
    return dis;
}

void clear_hash_tables()
{
   int i;
   for(i=0;i<L;i++) 
	{
		H1[i]=0;
		H2[i]=0; 
		H3[i]=0; 
	} 
}

double deviation(double *Array, int n) {
    double mean=0;
    double var=0;
    int i,j;
    for (i=0;i<n;i++){
        mean+=Array[i];
    }
    mean/=n;
    for(i=0;i<n;i++) {
        var+=(Array[i]-mean)*(Array[i]-mean);
    }
    var /= n;
    var = sqrt(var);
    return sqrt(var);
}
//
// preprocess functions
void initializing()
{
     int i,j, x1, x2;
     int count = 0;

	 ifstream FIC;
	 ofstream FIC2;
     FIC.open(File_Name);
     if ( FIC.fail() )
     {
           cout << "### Erreur open, File_Name " << File_Name << endl;
           exit(0);
     }
	 FIC >> N >> M;

	 P = new int [N];
	 P1= new int [N];
	 B = new int [N];

	 R = new int *[M];
	 for(i=0;i<M;i++)
		 R[i] = new int [N];
	 R1 = new int *[M];
	 for(i=0;i<M;i++)
		 R1[i] = new int [N];

     while ( ! FIC.eof() )
     {
         for(i=0;i<N;i++) FIC >> P[i];

		 for(i=0;i<M;i++)
		    for(j=0;j<N;j++)FIC >> R[i][j];
	     for(j=0;j<M;j++) FIC >> B[j];
     }
     FIC.close();
}

void initializing2()
{
    int i,j, x1, x2;
    int count = 0;

    ifstream FIC;
    ofstream FIC2;
    FIC.open(File_Name);
    if ( FIC.fail() )
    {
        cout << "### Erreur open, File_Name " << File_Name << endl;
        exit(0);
    }
    FIC >> N >> M;
    P = new int [N];
    P1= new int [N];
    B = new int [N];

    R = new int *[M];
    for(i=0;i<M;i++)
        R[i] = new int [N];
    R1 = new int *[M];
    for(i=0;i<M;i++)
        R1[i] = new int [N];

    while ( ! FIC.eof() )
    {
        for(i=0;i<N;i++) FIC >> P[i];
        for(j=0;j<M;j++) FIC >> B[j];
        for(i=0;i<M;i++)
            for(j=0;j<N;j++)FIC >> R[i][j];
        
    }
    FIC.close();
}

void initlization(Solution &S)
{
	int r;
	int flag,i,j,m,check;
	int unchecked[N];
	int uncheck_remain=N;
	S.IN=0;
	S.ON=0;
    S.f=0;
	for(m=0;m<M;m++) S.IW[m] = 0;
	for(i=0;i<N;i++) unchecked[i] = i;
	while(uncheck_remain>0) {
		r = rand()%uncheck_remain;
		check = unchecked[r];
		flag = 1;
		for(m=0; m<M; m++) if (S.IW[m] + R[m][check] > B[m]) {flag=0; break;}
		if(flag){
			S.X[check] = 1;
			for(m=0;m<M;m++) S.IW[m] += R[m][check];
			S.f+=P[check];
			S.S[S.IN] = check;
			S.IN++; 
		} else {
			S.X[check] = 0;
			S.NS[S.ON] = check;
			S.ON++;
		}
		unchecked[r] = unchecked[uncheck_remain-1];
		uncheck_remain--;
	}
}

void generate_base_solutions()
{
    int i, j;
    int min_f = 999999;
    int min_findex;
    int max_f = 0;
    int max_findex;
    for (i=0; i<NeedNumber; i++) {

        initlization(SAVE_SOLUTIONS[i]);
        if (SAVE_SOLUTIONS[i].f < min_f) {
            min_f = SAVE_SOLUTIONS[i].f;
            min_findex = i;
        } else if (SAVE_SOLUTIONS[i].f > max_f) {
            max_f = SAVE_SOLUTIONS[i].f;
            max_findex = i;
        }
    }
    for (i=0; i<Maxnumber-NeedNumber; i++) {
        initlization(SAVE_SOLUTIONS[min_findex]);
        if (SAVE_SOLUTIONS[min_findex].f > max_f) {
            max_f = SAVE_SOLUTIONS[min_findex].f;
            max_findex = min_findex;
        }
        if (SAVE_SOLUTIONS[min_findex].f > min_f) {
            min_f = 999999;
            for (j=0; j<NeedNumber; j++) {
                if (SAVE_SOLUTIONS[j].f < min_f) {
                    min_f = SAVE_SOLUTIONS[j].f;
                    min_findex = j;
                }
            }
        }
    }
    copy_sc(SAVE_SOLUTIONS[max_findex], G_BEST);
}

void assign_memery()
{
	int i, j, swap;
	SC.X      = new int [N];
	SC.S      = new int [N];
	SC.NS     = new int [N]; 
	SC.IW     = new int [M];
    SCbest.X      = new int [N];
    SCbest.S      = new int [N];
    SCbest.NS     = new int [N];
    SCbest.IW     = new int [M];
	S_BEST.X  = new int [N];
	S_BEST.S  = new int [N];
	S_BEST.NS = new int [N];
	S_BEST.IW = new int [M]; 
	G_BEST.X  = new int [N];
	G_BEST.S  = new int [N];
	G_BEST.NS = new int [N];
	G_BEST.IW = new int [M];
    G_BEST_history = new int [5000];
    iterator_time = new int [5000];
	order = new int [N];
    status = new int[999999];
	W1 = new int [N];
	W2 = new int [N];
	W3 = new int [N];
	
	H1 = new int [L];
	H2 = new int [L];
	H3 = new int [L];
    PR = new double [N];
    for(i=0;i<N;i++)
    {
    W1[i] = (int) pow(i+1,1.3);
    W2[i] = (int) pow(i+1,1.8);
    W3[i] = (int) pow(i+1,2.0);
    }
    for(i=0;i<NeedNumber+1;i++)
    {
    SAVE_SOLUTIONS[i].X  = new int [N];
    SAVE_SOLUTIONS[i].S  = new int [N];
    SAVE_SOLUTIONS[i].NS = new int [N];
    SAVE_SOLUTIONS[i].IW = new int [M];
    }
    dataM  = new double [N];
    dataNM = new double [N];
    Weight = new double [N];
    Weight2 = new double [N];
    NeedSearchIndex = new int [N];
    DidtNeedSearchIndex = new int[N];
    M_R = new int *[M];
    ReSearchList = new int [N];
    for(i=0;i<M;i++)
        M_R[i] = new int [N];

}

void free_memery()
{
    int i;
    delete[] SC.X;
    delete[] SC.S;
    delete[] SC.NS;
    delete[] SC.IW;

    delete[] SCbest.X;
    delete[] SCbest.S;
    delete[] SCbest.NS;
    delete[] SCbest.IW;

    delete[] S_BEST.X;
    delete[] S_BEST.S;
    delete[] S_BEST.NS;
    delete[] S_BEST.IW;

    delete[] G_BEST.X;
    delete[] G_BEST.S;
    delete[] G_BEST.NS;
    delete[] G_BEST.IW;

    delete[] W1;
    delete[] W2;
    delete[] W3;

    delete[] G_BEST_history;
    delete[] iterator_time;
    delete[] order;

    delete[] H1;
    delete[] H2;
    delete[] H3;

    delete[] PR;
    delete[] status;

    for(i=0;i<NeedNumber+1;i++)
    {
        delete[] SAVE_SOLUTIONS[i].X;
        delete[] SAVE_SOLUTIONS[i].S;
        delete[] SAVE_SOLUTIONS[i].NS;
        delete[] SAVE_SOLUTIONS[i].IW;
    }

    delete[] dataM;
    delete[] dataNM;
    delete[] Weight;
    delete[] Weight2;
    delete[] NeedSearchIndex;
    delete[] DidtNeedSearchIndex;
    delete[] ReSearchList;
    for(i=0;i<M;i++)
        delete[] M_R[i];
}

void compute_MR()
{
    int i,j;
    double m_r[N];
    int m_ro[N];


    for (i=0;i<M;i++) {
        for(j=0;j<N;j++) {
            m_r[j] = -100.0*P[j]/R[i][j];
            m_ro[j] = j;
        }
        quick_sort(m_r, N, m_ro);
        for(j=0;j<N;j++) {
            M_R[i][j] = m_ro[j];
        }
    }

}

void compute_value1()
{
	int i,j;
	for(j=0;j<N;j++) order[j] = j;
	for(j=0;j<N;j++)
	{
	    PR[j] = 0.0;
		for(i=0;i<M;i++)
		{
			PR[j] +=  (1.0*R[i][j]) / (1.0*B[i]) ;
		}

		PR[j] = 1.0*P[j]/PR[j];
	}

    quick_sort(PR, N, order);
}

void preprocessing()
{
	int i,j;
	compute_value1();
	for(j=0;j<N;j++) P1[j] = P[order[j]];
	for(i=0;i<M;i++)
	{
		for(j=0;j<N;j++) R1[i][j] = R[i][order[j]];
	}
	for(j=0;j<N;j++) P[j] = P1[j];
	for(i=0;i<M;i++)
	{
		for(j=0;j<N;j++) R[i][j] = R1[i][j];
	}
}

void out_line(int *itert, int *bestn, string outfile, string src)
{
    FILE *fp;
    char buff[80];
    sprintf(buff, "%s", (src).c_str());
    fp=fopen(buff, "a+");
    for (int i=0; i<history_offset; i++)
    fprintf(fp, "%d ", bestn[i]);
    fprintf(fp, "\n");
    for (int i=0; i<history_offset; i++)
    fprintf(fp, "%d ", itert[i]);
    fprintf(fp, "\n");
    fclose(fp);
}

void clear(string outfile, string src) {
    FILE *fp;
    char buff[80];
    sprintf(buff, "%s", (src+"info"+outfile.substr(20)).c_str());
    fp=fopen(buff, "w");
    fclose(fp);
}

void out_sol(Solution &S, string filename)
{
    int i;
    int r;
	FILE *fp;
	char buff[80];
    sprintf(buff,"%s.sol", filename.c_str());
    fp=fopen(buff,"a+");
    fprintf(fp,"N = %d  M = %d  f= %ld\n", N, M, S.f);
    for(i=0;i<N;i++)
    fprintf(fp,"%d\n", S.X[i]);
	fclose(fp);
}

void out_status(string filename)
{
    int i,j;
    FILE *fp;
    char buff[80];
    sprintf(buff, "%s.status", filename.c_str());
    fp = fopen(buff, "a+");
    // for(i=0;i<status_index;i++)
    fprintf(fp, "%lf ", EXACT_T);
    fprintf(fp, "\n");
    fclose(fp);
}

void out_resulting(string filename, string outfile)
{
    int i,j;
    FILE *fp;
    char buff[80];
    sprintf(buff,"%s",outfile.c_str());
    fp=fopen(buff,"a+");
    fprintf(fp,"%s  %d  %lf  %lf  %d\n",filename.c_str(),N,BestResult,CutTime,seeds);
    fclose(fp);
}

void statistics_info()
{
    int i,j;
    for (i=0; i<N; i++) {
        Weight[i]=0.0;
    }

    for (i=0; i<N; i++) {
        for (j=0; j<NeedNumber; j++) {
            if (SAVE_SOLUTIONS[j].X[i] == 1)
                Weight[i]+=1.0;
        }
    }
    for (i=0; i<N; i++) {
        Weight2[i] = Weight[i];
    }
}

void tabu_search(Solution &S)
{
	int i, j, j1, k, k0, x, y, v, u, iter ;
    long int Hx1, Hx2, Hx3;
    long int Hx11, Hx22, Hx33;
	int select, swap; 
	int IN_num, ON_num;
	int feasible;
	Neighbor best[ 50 ];
	Neighbor tabu_best[ 50 ];
	double current_time, starting_time;

	long int best_fc, f_c ;
	int  num_best;

	clear_hash_tables();
	Hx1 = 0;
	Hx2 = 0; 
	Hx3 = 0; 
	for(i=0;i<N;i++)
	{
		Hx1 += W1[i]*(S.X[i]); 
		Hx2 += W2[i]*(S.X[i]); 
		Hx3 += W3[i]*(S.X[i]); 
	}
	f = S.f; 
	f_best = -999999;
    copy_sc(S,S_BEST);
	iter = 0; 
	starting_time = clock(); 
	current_time = (double) (1.0*(clock() - starting_time)/CLOCKS_PER_SEC);  

	while( iter<IterMax)
	{
		best_fc = -999999999;
		num_best = 0 ;

		//1). the add neighborhodd
		for(k = 0; k < S.ON; k ++) // add a term
		{     
			j = S.NS[k];
			feasible=1;
			for(i=0;i<M;i++)   if(S.IW[i] + R[i][j] > B[i])  {feasible=0;break;}
			if (feasible==0) continue;
			Hx11 = Hx1 + W1[j];
			Hx22 = Hx2 + W2[j];
			Hx33 = Hx3 + W3[j];
			f_c = S.f + P[j];
			if(H1[Hx11%L]==1 && H2[Hx22%L]==1 && H3[Hx33%L]==1)  // if it is tabu
            {
				continue;                          
			}else{  
                if( f_c > best_fc )  
                {
                    best[ 0 ].x = j; 
                    best[ 0 ].type = 1;
                    best[ 0 ].IO = 0;
                    best[ 0 ].k = k;
                    best[ 0 ].f = f_c ;
                    best_fc  = f_c ; 
                    num_best = 1 ; 
                }
                else if( f_c == best_fc && num_best < 50 )
                {
                    best[ num_best ].x = j;  
                    best[ num_best ].type = 1 ;
                    best[ num_best ].IO = 0; 
                    best[ num_best ].k = k; 
                    best[ num_best ].f = f_c;  
                    num_best++ ;  
                }
            } 	
		}
		//drop
		for( k = 0; k < S.IN; k ++)  // drop a term
		{     
		    j = S.S[k];
			feasible=1;
			for(i=0;i<M;i++)   if(S.IW[i] - R[i][j] > B[i]) {feasible=0;break;}
			if (feasible==0) continue;
		    Hx11 = Hx1 - W1[j] ;
			Hx22 = Hx2 - W2[j] ;
			Hx33 = Hx3 - W3[j] ;
			
			f_c = S.f - P[j] ; 

		    if( H1[Hx11%L]==1 && H2[Hx22%L]==1 && H3[Hx33%L]==1 ) // if it is tabu
			{ 
				continue;                    
			} 
			else  
            {   
                if( f_c > best_fc )  
                {
                    best[ 0 ].x = j; 
                    best[ 0 ].type = 1;
                    best[ 0 ].IO = 1; 
                    best[ 0 ].k = k;
                    best[ 0 ].f = f_c ;
                    best_fc  = f_c ; 
                    num_best = 1 ; 
                }
                else if( f_c  == best_fc && num_best < 50 )
                {
                    best[ num_best ].x   = j ; 
                    best[ num_best ].type = 1 ;
                    best[ num_best ].IO = 1; 
                    best[ num_best ].k = k; 
                    best[ num_best ].f = f_c; 
                    num_best++ ;   
                }
            }              	
		}
		// swap



		for(x = 0; x < S.IN; x++)
		{ 
			for(y = 0; y < S.ON; y++)
			{
			    feasible=1;
			    for(i=0;i<M;i++) if(S.IW[i]+(R[i][S.NS[y]]-R[i][S.S[x]]) > B[i])   {feasible=0;break;}
                if (feasible==0) continue;
				f_c = S.f + (P[S.NS[y]]-P[S.S[x]]);
		        Hx11 = Hx1 + (W1[S.NS[y]]- W1[S.S[x]]) ;
			    Hx22 = Hx2 + (W2[S.NS[y]]- W2[S.S[x]]) ;
			    Hx33 = Hx3 + (W3[S.NS[y]]- W3[S.S[x]]) ; 
				
				if(H1[Hx11%L]==1 && H2[Hx22%L]==1 && H3[Hx33%L]==1 ) // if it is tabu
				{ 
					continue;
				}else{
					if( f_c > best_fc )  
					{
						best[ 0 ].x1 = x; 
						best[ 0 ].y1 = y;
						best[ 0 ].type = 2;
						best[ 0 ].IO = -1; 
						best[ 0 ].f  = f_c; 
						best_fc  = f_c ; 
						num_best = 1 ; 
					}
					else if( f_c == best_fc && num_best < 50 )
					{
						best[ num_best ].x1   = x ; 
						best[ num_best ].y1   = y ;
						best[ num_best ].type = 2 ;
						best[ num_best ].IO = -1 ; 
						best[ num_best ].f = f_c ; 
						num_best++ ;  
					}
				}
			}    
		}

		if( num_best != 0 ) //aspiration criterion 
        {
			select = rand() % num_best;
			f = best[select].f;
			if(best[select].type == 2)  
			{
				u = best[ select ].x1; 
				v = best[ select ].y1;  
				
				Hx1 += (W1[S.NS[v]]-W1[S.S[u]]); 
				Hx2 += (W2[S.NS[v]]-W2[S.S[u]]); 
				Hx3 += (W3[S.NS[v]]-W3[S.S[u]]); 
				H1[Hx1%L] = 1; 
				H2[Hx2%L] = 1; 
				H3[Hx3%L] = 1; 
				
				for(i=0;i<M;i++) 
				{
					S.IW[i] += (R[i][S.NS[v]] - R[i][S.S[u]]);  
				} 
				
				S.X[S.S[u]]  = 1 - S.X[S.S[u]]; 
				S.X[S.NS[v]] = 1 - S.X[S.NS[v]];
				
				swap    = S.S[u] ; 
				S.S[u]  = S.NS[v];
				S.NS[v] = swap ;  
				
				S.f = f;  
			} else if( best[select].type == 1 ) {
				j  = best[ select ].x; 
				k0 = best[ select ].k; 
				
				if(best[ select ].IO == 1)
				{	
					Hx1 -= W1[j]; 
					Hx2 -= W2[j]; 
					Hx3 -= W3[j]; 
					H1[Hx1%L] = 1; 
					H2[Hx2%L] = 1; 
					H3[Hx3%L] = 1; 
				
					for(i=0;i<M;i++) 
					{
						S.IW[i] -= R[i][j];  
					} 
					
					S.X[j] = 1 - S.X[j]; 
					for(i=k0;i<S.IN;i++) S.S[i] = S.S[i+1];
					S.IN -- ;
					
					S.NS[S.ON] = j ;
					S.ON ++ ; 
					S.f = f;   
						 
				} else if(best[ select ].IO == 0) {
					Hx1 += W1[j]; 
					Hx2 += W2[j]; 
					Hx3 += W3[j]; 
					H1[Hx1%L] = 1; 
					H2[Hx2%L] = 1; 
					H3[Hx3%L] = 1; 
				
					for(i=0;i<M;i++) 
					{
						S.IW[i] += R[i][j];  
					} 
					S.X[j] = 1 - S.X[j]; 
					for(i=k0;i<S.ON;i++) S.NS[i] = S.NS[i+1];
					S.ON -- ; 
					S.S[S.IN] = j; 
					S.IN++ ;
					S.f = f; 
				}	
			}
		}
		iter++;
		current_time = (double) (1.0*(clock()-starting_time)/CLOCKS_PER_SEC);
		if( S.f >= f_best)
		{   
			f_best = S.f;
            copy_sc(S, S_BEST);
			time_to_target = current_time; 
		}
		
	}
    copy_sc(S_BEST, S);
}

void updating_pop(Solution S, double beta=0.7)
{
    int i, j;
    int max_f, min_f, max_d, min_d, max_r, min_r;
    int score_min_index;
    double score_min;
    int temp_dis;
    int max_index;
    int ratio_valuesdiff;
    for(i=0;i<NeedNumber;i++){
        temp_dis = hamming_distance(SAVE_SOLUTIONS[i], S);
        if(temp_dis == 0) return;
    }
    int save_popmin[NeedNumber+1];
    int save_ratio[NeedNumber+1];
    int save_ratiomin[NeedNumber+1];
    double temp_score;
    for (i=0; i<NeedNumber+1; i++) {
        save_popmin[i] = 9999;
        save_ratio[i] = 0;
        save_ratiomin[i] = 9999;
    }
    max_f = 0;
    min_f = 999999;
    max_d = 0;
    min_d = 99999;
    max_r = 0;
    min_r = 99999;
    score_min = 99999;

    copy_sc(S, SAVE_SOLUTIONS[NeedNumber]);
    for(i=0;i<NeedNumber+1;i++)
    {
        if (SAVE_SOLUTIONS[i].f > max_f) {max_f = SAVE_SOLUTIONS[i].f; max_index=i;}
        if (SAVE_SOLUTIONS[i].f < min_f) min_f = SAVE_SOLUTIONS[i].f;
        for(j=0;j<N;j++) {
            if(SAVE_SOLUTIONS[i].X[j]==1) {
                save_ratio[i] += PR[j];
            }
        }
        for(j=0;j<NeedNumber+1;j++) {
            if(j==i) continue;
            temp_dis = hamming_distance(SAVE_SOLUTIONS[i], SAVE_SOLUTIONS[j]);
            if (temp_dis > max_d) max_d = temp_dis;
            if (temp_dis < min_d) min_d = temp_dis;
            if (temp_dis < save_popmin[i]) {
                save_popmin[i] = temp_dis;
            }
        }
    }


    for(i=0;i<NeedNumber+1;i++) {
        for(j=0;j<NeedNumber+1;j++) {
            if (i==j) continue;
            ratio_valuesdiff = abs(save_ratio[i] - save_ratio[j]);
            if (ratio_valuesdiff > max_r) max_r = ratio_valuesdiff;
            if (ratio_valuesdiff < min_r) min_r = ratio_valuesdiff;
            if (ratio_valuesdiff < save_ratiomin[i]) {
                save_ratiomin[i] = ratio_valuesdiff;
            }
        }
    }
    
    for(i=0;i<NeedNumber+1;i++)
    {
        if (i==max_index){
            temp_score=999999;
        } else {
            assert((max_d - min_d)!=0);
            assert((max_r - min_r)!=0);
            assert((max_f - min_f)!=0);
            temp_score = beta * ((1.0*(SAVE_SOLUTIONS[i].f - min_f)) / (1.0*(max_f - min_f))) + ((1-beta)/2) * ((1.0*(save_popmin[i] - min_d)) / (1.0*(max_d - min_d))) + ((1-beta)/2) * ((1.0*(save_ratiomin[i] - min_r)) / (1.0*(max_r - min_r)));
        }
        if (score_min > temp_score) {
            score_min = temp_score;
            score_min_index = i;
        }
    }
    copy_sc(SAVE_SOLUTIONS[NeedNumber], SAVE_SOLUTIONS[score_min_index]);
}

int supply_elements(Solution S, int num_need, int num_didtneed)
{
    int i,j;
    int flag;
    int supple_count=0;
    int m_order[M];
    int local_B[M];
    double items_need_m[M];
    
    for (i=0; i<M; i++) {
        local_B[i] = B[i];
    }
    for (i=0; i<M; i++) {
        items_need_m[i]=0;
        m_order[i] = i;
    }
    for (i=0; i<num_didtneed; i++) {
        if (S.X[DidtNeedSearchIndex[i]]==1) {
            for (j=0; j<M; j++)
            {
                local_B[j] -= R[j][DidtNeedSearchIndex[i]];
            }
        }
    }

    for (i=0;i<M;i++) {
        for (j=0;j<num_need;j++) {
            items_need_m[i] += R[i][NeedSearchIndex[j]];
        }
        items_need_m[i] = 100.0*local_B[i]/items_need_m[i];
    }
    quick_sort(items_need_m, M, m_order);

    for (i=0;i<N;i++) {
        flag = 1;
        for(j=0;j<num_need;j++) {
            if (M_R[m_order[0]][i] == NeedSearchIndex[j]) {
                flag = 0;
                break;
            }
        }
        if (flag == 1) {
            NeedSearchIndex[num_need++] = M_R[m_order[0]][i];
            supple_count++;
            for(j=0;j<num_didtneed;j++){
                if (DidtNeedSearchIndex[j] == M_R[m_order[0]][i]){
                    num_didtneed--;
                    DidtNeedSearchIndex[j] = DidtNeedSearchIndex[num_didtneed];
                    break;
                }
            }
        }
        if(supple_count==10){
            break;
        }
    }
    return num_need;
}

int cplex_search(Solution &S, int best_know, int num_need, int num_didtneed, int doubletime=1, int flag_add=1)
{

    int i,j;
    int size;
    int offset;
    int satisfy_count;
    int local_B[M];
    int most_need_mindex;
    double max_m=0;
    int combina[M];
    int forcom=0;
    double devia;
    double ea_start_time;
    
    if (flag_add==1) {
        num_need = supply_elements(S, num_need, num_didtneed);
        num_didtneed = N-num_need;
    }

    for (i=0; i<M; i++) {
        local_B[i] = B[i];
    }

    for (i=0; i<num_didtneed; i++) {
        if (S.X[DidtNeedSearchIndex[i]]==1) {
            for (j=0; j<M; j++)
            {
                local_B[j] -= R[j][DidtNeedSearchIndex[i]];
            }
        }
    }

    for(i=0;i<num_need;i++){
        if (S.X[NeedSearchIndex[i]]==1){
            best_know -= P[NeedSearchIndex[i]];
        }
    }

    // assert
   for(i=0;i<num_need;i++){
       satisfy_count=0;
       for(j=0;j<M;j++){
           if (local_B[j]>R[j][NeedSearchIndex[i]]){
               satisfy_count++;
           }
       }
       if (satisfy_count==M){
           break;
       }
   }
   if (satisfy_count!=M){
        redo = 1;
   } else {
        ea_start_time = clock();
        size = num_need;
        IloEnv env;
        // cplex model
        IloModel model(env);
        // // decision variables
        IloNumVarArray x(env);
        for (i = 0; i < size; i++) {
            stringstream name;
            name << "x(" << i << ")";
            x.add(IloBoolVar(env, 0, 1, name.str().c_str()));
        }
        IloExpr obj(env);
        for (i = 0; i < size; i++) {
            offset = NeedSearchIndex[i];
            obj += P[offset] * x[i];
        }
        model.add(IloMaximize(env, obj));

        for (i=0; i<M; i++) {
            IloExpr expr1(env);
            for (j=0; j<size; j++) {
                offset = NeedSearchIndex[j];
                expr1 += R[i][offset] * x[j];
            }
            model.add(expr1 <= local_B[i]);
            expr1.clear();
            expr1.end();
        }
        
        IloCplex solver(model);
        solver.setOut(env.getNullStream());
        solver.setWarning(env.getNullStream());
        solver.setParam(IloCplex::Param::Threads, 1);
        solver.setParam(IloCplex::Param::TimeLimit, cplex_tamx*doubletime);
        solver.setParam(IloCplex::Param::ClockType, 2);
        solver.setParam(IloCplex::Param::Simplex::Limits::LowerObj, best_know);
        solver.setParam(IloCplex::Param::RandomSeed, seeds);
        solver.solve();
        
        IloNumArray value_variables(env);
        solver.getValues(value_variables, x);

        SolutionState = solver.getStatus();
        status[status_index++] = SolutionState;
        // //release all the allocated resources

        S.f = 0;
        S.IN = 0;
        S.ON = 0;
        for(i=0; i<M; i++) {
            S.IW[i] = 0;
        }


        for(i=0;i<num_need;i++) {
            S.X[NeedSearchIndex[i]] = lrint(value_variables[i]);
        }

        for (i=0; i<N; i++)
        {
            S.f = S.f + S.X[i] * P[i];
            if (S.X[i]==1) {
                S.S[S.IN] = i;
                S.IN++;
                for (j=0; j<M; j++) {
                    S.IW[j] += R[j][i];
                }
            } else {
                S.NS[S.ON] = i;
                S.ON++;
            }
        }
        value_variables.clear();
        solver.clear();
        x.clear();
        obj.clear();
        model.end();
        solver.end();
        obj.end();
        x.end();
        env.end();
        EXACT_T += (double) (1.0*(clock()-ea_start_time)/CLOCKS_PER_SEC);
    }
    return num_need;
}

int get_someinformationfrompop(int k)
{
    int i,j;
    int nu;
    int result;
    for(i=0;i<N;i++)
    {
        nu=0;
        for(j=0;j<NeedNumber;j++){
            if(SAVE_SOLUTIONS[j].X[i]==1){
                nu+=1;
            }
        }
        if (nu>=k){
            result=i;
            break;
        }
    }
    return result;

}

int get_stage2list() {
    int i,j;
    double do_de[N];
    int offset=0;
    int deviation_value;
    int min_range;
    statistics_info();
    min_range = get_someinformationfrompop(1);
    for(i=min_range;i<N;i++) {
        do_de[offset++] =  Weight[i];
    }
    deviation_value = deviation(do_de, N-min_range);
    offset=0;
    for(i=N-1;i>=min_range;i--) {
        if (G_BEST.X[i] == 1 && Weight[i]<=NeedNumber-deviation_value){
            ReSearchList[offset++] = i;
        }else if (G_BEST.X[i] == 0 && Weight[i]>=deviation_value) {
            ReSearchList[offset++] = i;
        }
    }

    return offset;
}

int get_gbestcounter()
{
    int counter=0;
    int i;
    for (i=0;i<N;i++) {
        if(G_BEST.X[i]==1)
            counter++;
    }
    return counter;
}

void statistics_solutions(double beta)
{
    double r;
    int i;
    statistics_info();
    for (i=0;i<N;i++) {
        r = 1.0*(rand()%RAND_MAX)/RAND_MAX;
        Weight2[i] /= NeedNumber;
        Weight2[i] = beta*Weight2[i] + (1-beta)*((r+i*(1.0/N))/2);
        Weight2[i] *= 100;
    }
    for(i=0;i<N;i++) order[i]=i;
    quick_sort(Weight2, N, order);
}

void concreate_Sc()
{
    int i,j;
    double r, prob;
    int rand1, rand2;
    int cho_num;
    cho_num = NeedNumber/10;
    for(i=0;i<N;i++)
    {
        prob=0.0;
        for(j=0;j<cho_num;j++){
            rand1 = rand()%NeedNumber;
            if(SAVE_SOLUTIONS[rand1].X[i]==1){
                prob+=1.0;
            }
        }
        if (prob<cho_num/2){
            SC.X[i]=0;
        }else{
            SC.X[i]=1;
        }

        r = 1.0*(rand()%RAND_MAX)/RAND_MAX;
        if(r<1.0/(N*10)){
            SC.X[i]=1-SC.X[i];
        }
    }
}

int get_need_cplex_search(int k)
{
    int i,j;
    int len = NeedNumber/k;
    int need_num=0;
    int didtneed_num=0;
    int i_r;
    int rand_ratio = NeedNumber/3;
    int counter;
    int mid;
    double comp;

    counter = get_gbestcounter();
    // k = min(k, counter-1);
    mid = N - counter;
    for (i=0;i<N;i++) {
        if (i>=mid-k/2&&i<mid+k/2) {
            NeedSearchIndex[need_num++] = order[i];
        }else {
            DidtNeedSearchIndex[didtneed_num++] = order[i];
        }
    }
    return need_num;
}

int add_something(int re_n){
    int i,j,k;
    int flag;
    double r;
    int copyneedn = 0;
    int didneedn = 0;
    int min_range;
    int min_range2;
    int max_n=0;
    for (i=0;i<re_n;i++){
        NeedSearchIndex[copyneedn++] = ReSearchList[i];
        if (ReSearchList[i]>max_n){
            max_n=ReSearchList[i];
        }
    }
    min_range = get_someinformationfrompop(1);
    min_range2 = get_someinformationfrompop(NeedNumber/2);
    for(i=min_range2;i<max_n;i++){
        flag=0;
        for(j=0;j<copyneedn;j++) {
            if(NeedSearchIndex[j]==i){
                flag=1;
                break;
            }
        }
        if(flag==0){
            r = 1.0*(rand()%RAND_MAX)/RAND_MAX;
            if(r<0.1){
                NeedSearchIndex[copyneedn++]=i;
            }
        }
    }

    for(i=min_range;i<min_range2;i++){
        flag=0;
        for(j=0;j<M;j++){
            for(k=0;k<N/50;k++){
                if(M_R[j][k]==i){
                    flag=1;
                    break;
                }
            }
            
        }
        if(flag==0){
            for(j=0;j<copyneedn;j++) {
                if(NeedSearchIndex[j]==i){
                    flag=1;
                    break;
                }
            }
        }
        if(flag==0){
            r = 1.0*(rand()%RAND_MAX)/RAND_MAX;
            if(r<0.7){
                NeedSearchIndex[copyneedn++]=i;
            }
        }
    }

    for(i=0;i<N;i++){
        flag=1;
        for(j=0;j<copyneedn;j++)
        {
            if (i == NeedSearchIndex[j]) {
                flag=0;
                break;
            }
        }
        if(flag==1){
            DidtNeedSearchIndex[didneedn++] = i;
        }
    }
    return copyneedn;
}

void cplex_loop_search()
{
    int i,j;
    int steps_index = 0;
    int cplex_started;
    int cplex_step=50;
	int Hx1, Hx2, Hx3; 
    int Hx11, Hx22, Hx33; 
    int forget_index = 0;
    int cplex_one_search_times;
    int assess;
    double random_ratio;
    int ran1, ran2;
    int display=1000;
    int Research_number;
    int num_count = 0;
    int runinng_time;
    int runinng_time2;
    int e_time;
    int mul_running;
    int upp_round, low_round;
    int search_number;
    int didtneed;
    int act_index=0;
    int flag;
    int half;
    int POP_index;
    double steps[N];
    int show_values;
    int research_step;
    int better_flag;
    double r;
    starting_time = clock();
    mul_running=1;
    time_to_target = 0;
    random_ratio=0.6;
    runinng_time = 1;
    generate_base_solutions();
    compute_MR();
    for(i=0;i<NeedNumber;i++) {
        tabu_search(SAVE_SOLUTIONS[i]);
        if (SAVE_SOLUTIONS[i].f > G_BEST.f) {
            copy_sc(SAVE_SOLUTIONS[i], G_BEST);
            time_one_run=(double) (1.0*(clock()-starting_time)/CLOCKS_PER_SEC);
            G_BEST_history[history_offset] = G_BEST.f;
            iterator_time[history_offset++] = int(time_one_run);
        }
    }
    
    while(time_to_target < tmax) {
        statistics_solutions(random_ratio);
        concreate_Sc();

        SolutionState=0;
        search_number = get_need_cplex_search(N/4);
        search_number = cplex_search(SC, G_BEST.f, search_number, N-search_number, runinng_time);
        if (redo == 1) {
            redo = 0;
            break;
        }

        if (SC.f > G_BEST.f) {
            better_flag=1;
            copy_sc(SC, G_BEST);
            while(SC.f > G_BEST.f && SolutionState!=1){
                copy_sc(SC, G_BEST);
                mul_running*=2;
                search_number = cplex_search(SC, G_BEST.f, search_number, N-search_number, runinng_time*mul_running, 0);
            }
            time_one_run=(double) (1.0*(clock()-starting_time)/CLOCKS_PER_SEC);
            mul_running=1;
            G_BEST_history[history_offset] = G_BEST.f;
            iterator_time[history_offset++] = int(time_one_run);
            updating_pop(SC);
        }

        updating_pop(SC);
        if(num_count>NeedNumber && (better_flag==1||num_count%NeedNumber==0)){
            better_flag=0;
            e_time=10;
            Research_number = get_stage2list();
            research_step=0;
            copy_sc(G_BEST, SCbest);
            while (research_step<e_time){
                copy_sc(SCbest, SC);
                SolutionState=0;
                search_number = add_something(Research_number);
                search_number = cplex_search(SC, G_BEST.f, search_number, N-search_number, runinng_time);
                
                if (SC.f > G_BEST.f) {
                    better_flag=1;
                    copy_sc(SC, G_BEST);
                    while(SC.f > G_BEST.f && SolutionState!=1){
                        copy_sc(SC, G_BEST);
                        mul_running*=2;
                        search_number = cplex_search(SC, G_BEST.f, search_number, N-search_number, runinng_time*mul_running, 0);
                    }
                    time_one_run=(double) (1.0*(clock()-starting_time)/CLOCKS_PER_SEC);
                    mul_running=1;
                    G_BEST_history[history_offset] = G_BEST.f;
                    iterator_time[history_offset++] = int(time_one_run);
                }
                updating_pop(SC);
                research_step++;
            }
        }
        
        num_count+=1;
        time_to_target=(double) (1.0*(clock()-starting_time)/CLOCKS_PER_SEC);
    }
}

int main(int argc, char **argv)
{
    string data_out;
    int i, j;
    int instance_type;
    tmax = atoi(argv[1]);
    cplex_tamx = atoi(argv[2]);
    seeds = atoi(argv[3]);
    instance_type = atoi(argv[4]);
    File_Name = argv[5];
    data_out = argv[6];
    srand(seeds);
    L = 2*pow(10,7);
    if (instance_type == 1) {
        initializing();
    }
    else if (instance_type == 2) {
        initializing2();
    }
    else{
        cout << "bad command instance_type = " << instance_type <<endl;
        exit(1);
    }
    assign_memery();
    preprocessing();
    cplex_loop_search();
    CutTime = time_one_run;
    BestResult = G_BEST.f;
    out_sol(G_BEST, File_Name);
    out_status(data_out);
    out_line(iterator_time, G_BEST_history, File_Name, data_out);
    free_memery();
	return 1;
}
