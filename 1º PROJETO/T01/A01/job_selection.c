////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// AED, 2020/2021
//
// TODO: Diana Elisabete Siso Oliveira, nº 98607
// TODO: Miguel Rocha Ferreira, nº 98599
// TODO: Paulo Guilherme Soares Pereira, nº 98430
//
// Brute-force solution of the generalized weighted job selection problem
//
// Compile with "cc -Wall -O2 job_selection.c -lm" or equivalent
//
// In the generalized weighted job selection problem we will solve here we have T programming tasks and P programmers.
// Each programming task has a starting date (an integer), an ending date (another integer), and a profit (yet another
// integer). Each programming task can be either left undone or it can be done by a single programmer. At any given
// date each programmer can be either idle or it can be working on a programming task. The goal is to select the
// programming tasks that generate the largest profit.
//
// Things to do:
// 0. (mandatory)
// Place the student numbers and names at the top of this file.
// 1. (highly recommended)
// Read and understand this code.
// 2. (mandatory)
// Solve the problem for each student number of the group and for
// N=1, 2, ..., as higher as you can get and
// P=1, 2, ... min(8,N)
// Present the best profits in a table (one table per student number).
// Present all execution times in a graph (use a different color for the times of each student number).
// Draw the solutions for the highest N you were able to do.
// 3. (optional)
// Ignore the profits (or, what is the same, make all profits equal); what is the largest number of programming
// tasks that can be done?
// 4. (optional)
// Count the number of valid task assignments. Calculate and display an histogram of the number of occurrences of
// each total profit. Does it follow approximately a normal distribution?
// 5. (optional)
// Try to improve the execution time of the program (use the branch-and-bound technique).
// Can you use divide and conquer to solve this problem?
// Can you use dynamic programming to solve this problem?
// 6. (optional)
// For each problem size, and each student number of the group, generate one million (or more!) valid random
// assignments and compute the best solution found in this way. Compare these solutions with the ones found in
// item 2.
// 7. (optional)
// Surprise us, by doing something more!
// 8. (mandatory)
// Write a report explaining what you did. Do not forget to put all your code in an appendix.
//
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>
#include "elapsed_time.h"
#include <unistd.h>
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Random number generator interface (do not change anything in this code section)
//
// In order to ensure reproducible results on Windows and GNU/Linux, we use a good random number generator, available at
// https://www-cs-faculty.stanford.edu/~knuth/programs/rng.c
// This file has to be used without any modifications, so we take care of the main function that is there by applying
// some C preprocessor tricks
//
#define main rng_main // main gets replaced by rng_main
#ifdef __GNUC__
int rng_main() __attribute__((__unused__)); // gcc will not complain if rnd_main() is not used
#endif
#include "rng.c"
#undef main // main becomes main again
#define srandom(seed) ran_start((long)seed) // start the pseudo-random number generator
#define random() ran_arr_next() // get the next pseudo-random number (0 to 2^30-1)
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// problem data (if necessary, add new data fields in the structures; do not change anything else in this code section)
//
// on the data structures declared below, a comment starting with
// * a I means that the corresponding field is initialized by init_problem()
// * a S means that the corresponding field should be used when trying all possible cases
                   
// * IS means both (part initialized, part used)
//
#if 1
#define MAX_T 64 // maximum number of programming tasks
#define MAX_P 10 // maximum number of programmers
typedef struct {
int starting_date; // I starting date of this task
int ending_date; // I ending date of this task
int profit; // I the profit if this task is performed
int assigned_to; // S current programmer number this task is assigned to (use -1 for no assignment)
} task_t;
typedef struct {
int NMec; // I student number
int T; // I number of tasks
int P; // I number of programmers
int I; // I if 1, ignore profits
int total_profit; // S current total profit
double cpu_time; // S time it took to find the solution
task_t task[MAX_T]; // IS task data
int busy[MAX_P]; // S for each programmer, record until when she/he is busy (-1 means idle)
char dir_name[16]; // I directory name where the solution file will be created
char file_name[64]; // I file name where the solution data will be stored
} problem_t;
int compare_tasks_ending_2(const void *t1,const void *t2){
int d1,d2;
d1 = ((task_t *)t1)->ending_date;
d2 = ((task_t *)t2)->ending_date;
if(d1 != d2)
return (d1 < d2) ? -1 : +1;
d1 = ((task_t *)t1)->starting_date;
d2 = ((task_t *)t2)->starting_date;
if(d1 != d2)
return (d1 < d2) ? -1 : +1;
return 0;
}
int compare_tasks(const void *t1,const void *t2) {
int d1,d2;
d1 = ((task_t *)t1)->starting_date;
d2 = ((task_t *)t2)->starting_date;
if(d1 != d2)
return (d1 < d2) ? -1 : +1;
d1 = ((task_t *)t1)->ending_date;
d2 = ((task_t *)t2)->ending_date;
if(d1 != d2)
return (d1 < d2) ? -1 : +1;
return 0;
}
int compare_tasks_ending(const void *t1,const void *t2) { 
int d1,d2;
d1 = ((task_t *)t1)->ending_date;
d2 = ((task_t *)t2)->ending_date;
if(d1 != d2)
return (d1 > d2) ? -1 : +1;
d1 = ((task_t *)t1)->starting_date;
d2 = ((task_t *)t2)->starting_date;
if(d1 != d2)
return (d1 > d2) ? -1 : +1;
return 0;
}
void init_problem(int NMec,int T,int P,int ignore_profit,problem_t *problem, int optionChosen) {
int i,r,scale,span,total_span;
int *weight;
//
// input validation
//
if(NMec < 1 || NMec > 999999) {
fprintf(stderr,"Bad NMec (1 <= NMex (%d) <= 999999)\n",NMec);
exit(1);
}
if(T < 1 || T > MAX_T) {
fprintf(stderr,"Bad T (1 <= T (%d) <= %d)\n",T,MAX_T);
exit(1);
}
if(P < 1 || P > MAX_P) {
fprintf(stderr,"Bad P (1 <= P (%d) <= %d)\n",P,MAX_P);
exit(1);
}
//
// the starting and ending dates of each task satisfy 0 <= starting_date <= ending_date <= total_span
//
total_span = (10 * T + P - 1) / P;
if(total_span < 30)
total_span = 30;
//
// probability of each possible task duration
//
// task span relative probabilities
//
// | 0 0 4 6 8 10 12 14 16 18 | 20 | 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 | smaller than 1
// | 0 0 2 3 4 5 6 7 8 9 | 10 | 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 | 30 31 ... span
//
weight = (int *)alloca((size_t)(total_span + 1) * sizeof(int)); // allocate memory (freed automatically)
if(weight == NULL) {
                   
printf(stderr,"Strange! Unable to allocate memory\n");
exit(1);
}
#define sum1 (298.0) // sum of weight[i] for i=2,...,29 using the data given in the comment above
#define sum2 ((double)(total_span - 29)) // sum of weight[i] for i=30,...,data_span using a weight of 1
#define tail 100
scale = (int)ceil((double)tail * 10.0 * sum2 / sum1); // we want that scale*sum1 >= 10*tail*sum2, so that large task
if(scale < tail) // durations occur 10% of the time
scale = tail;
weight[0] = 0;
weight[1] = 0;
for(i = 2;i <= 10;i++)
weight[i] = scale * (2 * i);
for(i = 11;i <= 29;i++)
weight[i] = scale * (30 - i);
for(i = 30;i <= total_span;i++)
weight[i] = tail;
#undef sum1
#undef sum2
#undef tail
//
// accumulate the weigths (cummulative distribution)
//
for(i = 1;i <= total_span;i++)
weight[i] += weight[i - 1];
//
// generate the random tasks
//
srandom(NMec + 314161 * T + 271829 * P);
problem->NMec = NMec;
problem->T = T;
problem->P = P;
problem->I = (ignore_profit == 0) ? 0 : 1;
for(i = 0;i < T;i++) {
//
// task starting an ending dates
//
r = 1 + (int)random() % weight[total_span]; // 1 .. weight[total_span]
for(span = 0;span < total_span;span++)
if(r <= weight[span])
break;
problem->task[i].starting_date = (int)random() % (total_span - span + 1);
problem->task[i].ending_date = problem->task[i].starting_date + span - 1;
//
// task profit
//
// the task profit is given by r*task_span, where r is a random variable in the range 50..300 with a probability
// density function with shape (two triangles, the area of the second is 4 times the area of the first)
//
// *
// /| *
// / | *
// / | *
// *---*---------------*
// 50 100 150 200 250 300
//
scale = (int)random() % 12501; // almost uniformly distributed in 0..12500
if(scale <= 2500)
problem->task[i].profit = 1 + round((double)span * (50.0 + sqrt((double)scale)));
else
problem->task[i].profit = 1 + round((double)span * (300.0 - 2.0 * sqrt((double)(12500 - scale))));
}
//
// sort the tasks by the starting date
//OPÇÕES DE ORDENAÇÃO CONFORME OS INPUTS
if (problem->I == 1 && optionChosen == 3) {
qsort((void *)&problem->task[0],(size_t)problem->T,sizeof(problem->task[0]),compare_tasks_ending_2);
}
else if (problem->I == 0 && optionChosen == 1) {
qsort((void *)&problem->task[0],(size_t)problem->T,sizeof(problem->task[0]),compare_tasks_ending);
}
else if (problem->I == 0 && optionChosen == 2) {
qsort((void *)&problem->task[0],(size_t)problem->T,sizeof(problem->task[0]),compare_tasks_ending_2);
}
else if (problem->I == 1 && optionChosen == 2) {
qsort((void *)&problem->task[0],(size_t)problem->T,sizeof(problem->task[0]),compare_tasks);
}
else if (problem->I == 1 && optionChosen == 1) {
qsort((void *)&problem->task[0],(size_t)problem->T,sizeof(problem->task[0]),compare_tasks);
}
else if (problem->I == 1 && optionChosen == 4) {
qsort((void *)&problem->task[0],(size_t)problem->T,sizeof(problem->task[0]),compare_tasks);
}
else if (problem->I == 1 && optionChosen == 5) {
qsort((void *)&problem->task[0],(size_t)problem->T,sizeof(problem->task[0]),compare_tasks);
}
//
// finish
//
if(problem->I != 0)
for(i = 0;i < problem->T;i++)
problem->task[i].profit = 1;
#define DIR_NAME problem->dir_name
if(snprintf(DIR_NAME,sizeof(DIR_NAME),"%06d",NMec) >= sizeof(DIR_NAME)) {
fprintf(stderr,"Directory name too large!\n");
exit(1);
}
#undef DIR_NAME
#define FILE_NAME problem->file_name
if(snprintf(FILE_NAME,sizeof(FILE_NAME),"%06d/%02d_%02d_%d.txt",NMec,T,P,problem->I) >= sizeof(FILE_NAME)){
fprintf(stderr,"File name too large!\n");
exit(1);
}
#undef FILE_NAME
}
#endif
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// problem solution (place your solution here)
//FUNÇÕES!!
//FUNÇÃO 1 - INÍCIO
static int MelhorComb(int tarefa, int **MatrizCompativeis, problem_t *problem, int *jaEscolhida, int *tarefasProgramador, int totalTasks) {
int counter = 0;
for (int element=tarefa; element<problem->T; element++) {
if(MatrizCompativeis[tarefa][element] == 1) {
int flag=0;
for (int e2=0; e2 <(counter); e2++) {
if ((MatrizCompativeis[jaEscolhida[e2]][element] != 1) || (jaEscolhida[e2] == element)) {
flag = 1; break;
}
}
if (flag == 1) { continue; }
if (flag == 0){
jaEscolhida[counter] = element;
counter = counter + 1;
}
}
else { continue; }
}
for (int element=tarefa; element >= 0; element--) {
if(MatrizCompativeis[tarefa][element] == 1) {
int flag=0;
for (int e2=0; e2 <(counter); e2++) {
if ((MatrizCompativeis[jaEscolhida[e2]][element] != 1) || (jaEscolhida[e2] == element)){
flag = 1; break;
}
}
if (flag == 1) { continue; }
if (flag == 0){
jaEscolhida[counter] = element;
counter = counter +1;
}
}
else { continue; }
}
if (totalTasks < counter) {
for (int x=0; x<problem->T; x++) {
tarefasProgramador[x] = -1;
}
totalTasks = counter;
for (int x=0; x<problem->T; x++) {
tarefasProgramador[x] = jaEscolhida[x];
}
}
return counter;
}
//FUNÇÃO 1 - FIM
//FUNÇÃO 2 - INÍCIO
static int funcaoTask(problem_t *problem, int tarefa, int programador, int nrTasksTotal) {
problem->busy[programador]=-1;
int *tarefasProgramador= (int *) malloc(sizeof(int)*problem->T); //alocar memória para o array tarefasprogramador
for(int m=0; m<problem->T;m++) //Inicializar o vetor tarefasProgramador a -1 para cada programador
{ tarefasProgramador[m]=-1; }
int nrTasks=0;
for(int k=tarefa; k<problem->T;k++){ //Para cada task
if(problem->task[k].assigned_to==-1) {
if(problem->busy[programador]==-1) {//Caso o programador esteja disponível
if(problem->task[k].assigned_to==-1){ //Caso a task não esteja atribuída
tarefasProgramador[nrTasks]=k; //Guarda a task num vetor
nrTasks++; //Incrementa o nr de tasks
problem->busy[programador]=problem->task[k].ending_date; //Põe o programador busy até à data de fim da tarefa
}
} else {
if(problem->task[k].starting_date>problem->busy[programador]) {//Caso a data de inicio da tarefa seja maior que o fim da tarefa que o programador está a fazer
problem->busy[programador]=problem->task[k].ending_date; //Põe o programador busy até à data de fim da tarefa
tarefasProgramador[nrTasks]=k; //Guarda a task num vetor
nrTasks++;
}
}
}
}
problem->busy[programador] = problem->task[tarefa].starting_date;
for (int element = tarefa; element>0; element--) {
if(problem->task[element].assigned_to==-1) {
if (problem->task[element].ending_date<problem->busy[programador]) {
tarefasProgramador[nrTasks]=element;
problem->busy[programador]=problem->task[element].starting_date;
nrTasks++;
}
}
}
if(nrTasks>nrTasksTotal) {//Caso o nr de tasks seja maior que o total
for(int i=0;i<problem->T;i++) {//Para cada task
if(problem->task[i].assigned_to==programador) {//Caso alguma task esteja atribuida ao programador p é eliminado o registo
problem->task[i].assigned_to=-1;
}
}
nrTasksTotal=nrTasks; //Nr tasks total passa a ser o nr tasks
for(int i=0; i<problem->T;i++){ //Para cada task
if(tarefasProgramador[i]!=-1) {//Se o vetor tarefas tiver tarefas
problem->task[tarefasProgramador[i]].assigned_to=programador; //Atribui o valor ao assigned to
}
}
}
return nrTasks; //NR Tasks maximo ate ao momento que o programador pode fazer
}
//FUNÇÃO 2 - FIM
static int nrComb=0;
//FUNÇÃO 3 - INÍCIO
void addToArray(int arr[], int n, int**combinacoes) //Função que coloca as combinações no array combinações. Cada vez que é usada a variável nrComb
{ //é incrementada e funciona como índice para cada combinação. O seu valor final é o nr de combinações.
for (int i = 0; i < n; i++) { //O valor atribuído é 1 se a tarefa for para ser feita e 0 se não for para ser feita
combinacoes[nrComb][i]=arr[i];
// printf("%d ",arr[i]);
}
nrComb++;
//printf("\n");
}
//FUNÇÃO 3 - FIM
//FUNÇÃO 4 - INÍCIO
void gerarCombinacoes(int n, int arr[], int i,int **combinacoes) //Função que gera as combinações binárias
{
if (i == n) {
addToArray(arr, n,combinacoes);
return;
}
arr[i] = 0;
gerarCombinacoes(n, arr, i + 1,combinacoes);
arr[i] = 1;
gerarCombinacoes(n, arr, i + 1,combinacoes);
}
//FUNÇÃO 4 - FIM
//FUNÇÃO 5 - INÍCIO
void function(int *comb, int **tarefasProgramador, problem_t *problem, int *melhorAssignedTo) {
static int nrTasksGeral=0; //Define-se a variável nrTasksGeral (que vai guardar o melhor número de tasks realizadas possível) a 0
int profitAtual = 0; //Inicializa-se a variável profitAtual(que vai guardar o profit)
static int profitGeral=0;
int nrTasks=0;
int stop = 0;
for(int i=0;i<problem->P;i++){ //Inicializar o vetor tarefasProgramador a -1
problem->busy[i]=-1;
for(int k=0;k<problem->T;k++){
tarefasProgramador[i][k]=-1;
if (stop < problem->T) {
problem->task[k].assigned_to=-1;
stop++;
}
}
}
for(int prog=0;prog<problem->P;prog++) {//Para cada programador
for(int tar=0;tar<problem->T;tar++) {
if(comb[tar]==1) {//Caso a tarefa tar da combinacao comb possa ser feita
if(problem->busy[prog]==-1) { //Caso o programador esteja disponível
if(problem->task[tar].assigned_to==-1) {
tarefasProgramador[prog][nrTasks]=tar;
problem->busy[prog]=problem->task[tar].ending_date;
problem->task[tar].assigned_to=prog;
nrTasks++;
profitAtual=profitAtual+problem->task[tar].profit;
}
}
else { //Caso o programador esteja ocupado
if(problem->task[tar].assigned_to==-1){
if(problem->busy[prog]<problem->task[tar].starting_date){
tarefasProgramador[prog][nrTasks]=tar;
problem->busy[prog]=problem->task[tar].ending_date;
problem->task[tar].assigned_to=prog;
nrTasks++;
profitAtual=profitAtual+problem->task[tar].profit;
}
}
}
}
}
}
int flagE=0;
for(int i=0;i<problem->T;i++) {//Para cada elemento da combinacao
if(comb[i]==1) {//Caso a task tenha que ser realizada
if(problem->task[i].assigned_to==-1) {//Caso a task não tenha sido atribuída
flagE=1;
break;
}
}
}
                   
if(flagE==0){ //Caso todas as tasks que tinham que ser feitas tiverem sido feitas
if(profitAtual>profitGeral) {
for(int i=0;i<problem->T;i++) { //Inicializar o vetor melhorAssignedTo a -1
melhorAssignedTo[i]=-1;
}
nrTasksGeral=nrTasks;
profitGeral=profitAtual;
for(int i=0;i<problem->P;i++) {
for(int k=0;k<problem->T;k++) {
if(tarefasProgramador[i][k]!=-1) { //Caso o elemento seja uma tarefa
melhorAssignedTo[tarefasProgramador[i][k]]=i;
}
}
}
}
}
problem->total_profit=profitGeral;
}
//FUNÇÃO 5 - FIM
//FUNÇÃO 6 - INÍCIO
void generateAllBinaryStrings(int n, int arr[], int i, int **tarefasProgramador, int *melhorAssignedTo, problem_t *problem) //Função que gera as combinações binárias
{
if (i == n) {
if (problem->T < problem->P) {
function(arr, tarefasProgramador, problem, melhorAssignedTo);
}
else {
int contadorUm = 0;
for (int a=0; a<problem->T; a++) {
if (arr[a] == 1) {
contadorUm++;
}
}
if (contadorUm >= problem->P) {
function(arr, tarefasProgramador, problem, melhorAssignedTo); //quando já fez a combinação ele corre a função
}
}
return;
}
arr[i] = 0;
generateAllBinaryStrings(n, arr, i + 1, tarefasProgramador, melhorAssignedTo, problem);
arr[i] = 1;
generateAllBinaryStrings(n, arr, i + 1, tarefasProgramador, melhorAssignedTo, problem);
}
//FUNÇÃO 6 - FIM
//FUNÇÃO 7 - SOLVE
static void solve(problem_t *problem, int optionChosen)
{
FILE *fp;
int i;
(void)mkdir(problem->dir_name,S_IRUSR | S_IWUSR | S_IXUSR);
fp = fopen(problem->file_name,"w");
if(fp == NULL) {
fprintf(stderr,"Unable to create file %s (maybe it already exists? If so, delete it!)\n",problem->file_name);
exit(1);
}
//
// solve
problem->cpu_time = cpu_time();
printf("Aguarde...\n");
if (problem->I == 1) {
if (optionChosen == 1) {
fprintf(fp, "----- Solução a ignorar os lucros! -----\n");
int numeroTasksTotal;
int numeroTasksProgramador;
for (int i=0;i<problem->T;i++) { //Inicializar os vetores assigned to com T tarefas
problem->task[i].assigned_to=-1;
}
for (int i=0;i<problem->P;i++){ //Inicializar o vetor Busy com P espaços
problem->busy[i]=-1;
}
int quantasTasks = 0;
for(int p=0; p<problem->P; p++) { //Para cada programador
fprintf(fp,"\nPROGRAMADOR %d\n",(p+1));
numeroTasksProgramador=0; //Numero de tasks que cada programador vai fazer
numeroTasksTotal=0; //Melhor numero de tasks que cada programador vai fazer
for(int t=0;t<problem->T;t++) {//Para cada task de início (o programa vai correr a comecar em 0, 1, 2...)
numeroTasksProgramador=funcaoTask(problem,t,p,numeroTasksTotal); //Chama a função
if(numeroTasksProgramador>numeroTasksTotal){ //Se o numero de tasks devolvido pela funcao for maior substitui o nr de tasks total
numeroTasksTotal=numeroTasksProgramador;
}
}
for(int i=0;i<problem->T;i++){
if(problem->task[i].assigned_to==p){
quantasTasks++;
fprintf(fp, "Tarefa que começa em %d e acaba em %d\n", problem->task[i].starting_date, problem->task[i].ending_date);
}
}
}
printf("Numero de tasks: %d\n", quantasTasks);
}
if (optionChosen == 2) {
fprintf(fp, "----- Solução a ignorar os lucros! -----\n");
int **MatrizCompativeis;
MatrizCompativeis = malloc(problem->T * sizeof(int*));
for (int i=0; i<problem->T; i++) { MatrizCompativeis[i] = malloc(problem->T * sizeof(int)); }
for (int t1=0; t1<problem->T; t1++) {
for (int t2=t1; t2 < problem->T; t2++) {
if (t1==t2) { MatrizCompativeis[t1][t2] = 1; MatrizCompativeis[t2][t1] = 1; }
else {
if (problem->task[t1].ending_date < problem->task[t2].starting_date) { MatrizCompativeis[t1][t2] = 1; MatrizCompativeis[t2][t1] = 1; }
else { MatrizCompativeis[t1][t2] = 0; MatrizCompativeis[t2][t1] = 0; }
}
}
}
int nrTasks = 0;
for(int p=0; p<problem->P; p++) {
int *tarefasProgramador=(int *) malloc(sizeof(int)*(problem->T));
int *jaEscolhida=(int *) malloc(sizeof(int)*(problem->T));
for(int m=0; m<problem->T;m++) { tarefasProgramador[m]=-1; }
fprintf(fp, "\nPROGRAMADOR %d\n", p+1);
int totalTasks = 0;
int tasksValidas = 0;
for (int tarefa=0; tarefa<problem->T; tarefa++) {
for (int i=0; i<problem->T; i++) { jaEscolhida[i]=-1; }
tasksValidas = MelhorComb(tarefa, MatrizCompativeis,problem,jaEscolhida,tarefasProgramador,totalTasks);
if (tasksValidas > totalTasks) { totalTasks=tasksValidas;}
}
for (int x=0; x<problem->T; x++) {
if (tarefasProgramador[x] != -1) {
nrTasks++;
fprintf(fp, "Tarefa que começa em %d e acaba em %d\n", problem->task[tarefasProgramador[x]].starting_date, problem->task[tarefasProgramador[x]].ending_date);
for (int coluna = 0; coluna<problem->T;coluna++) { MatrizCompativeis[tarefasProgramador[x]][coluna] = 0; MatrizCompativeis[coluna][tarefasProgramador[x]] = 0; }
}
}
free(tarefasProgramador);
free(jaEscolhida);
}
printf("Numero de tasks: %d\n", nrTasks);
free(MatrizCompativeis);
}
if (optionChosen == 3) {
int *Comb=(int *) malloc(sizeof(int)*(problem->T));
int counter = 0;
for (int i=0; i<problem->T; i++) { problem->task[i].assigned_to=-1; }
for (int p=1; p<=problem->P; p++){
for (int i=0; i<problem->T; i++) { Comb[i] = -1; }
for (int task=0; task<problem->T; task++) {
if (problem->task[task].assigned_to!= -1) { continue; }
if (problem->busy[p] == -1) {
problem->task[task].assigned_to=p;
problem->busy[p]=problem->task[task].ending_date;
Comb[counter]=task;
counter++;
}
else {
if (problem->busy[p]<problem->task[task].starting_date) {
problem->task[task].assigned_to=p;
problem->busy[p]=problem->task[task].ending_date;
Comb[counter]=task;
counter++;
}
}
}
for (int task=0; task<counter; task++) {
int duration1 = problem->task[Comb[task]].ending_date - problem->task[Comb[task]].starting_date;
for (int element=0; element<problem->T; element++) {
int duration2= problem->task[element].ending_date - problem->task[element].starting_date;
if (problem->task[element].assigned_to ==-1) {
if (task == 0) {
if ((problem->task[element].ending_date < problem->task[Comb[task+1]].starting_date) && (duration2>duration1)){
problem->task[Comb[task]].assigned_to=-1;
problem->task[element].assigned_to= p;
Comb[task] = element;
}
}
else if (task== (counter -1)) {
if ((problem->task[element].starting_date > problem->task[Comb[task-1]].ending_date) && (duration2>duration1)){
problem->task[Comb[task]].assigned_to=-1;
problem->task[element].assigned_to= p;
Comb[task] = element;
}
}
else {
if ((problem->task[element].starting_date > problem->task[Comb[task-1]].ending_date) && (problem->task[element].ending_date < problem->task[Comb[task+1]].starting_date) && (duration2>duration1)){
problem->task[Comb[task]].assigned_to=-1;
problem->task[element].assigned_to= p;
Comb[task] = element;
}
}
}
}
}
fprintf(fp,"\nPROGRAMADOR: %d\n", p);
for (int task = 0; task<problem->T; task++) {
if (Comb[task] != -1) {
fprintf(fp,"Tarefa que começa em %d e acaba em %d\n", problem->task[Comb[task]].starting_date, problem->task[Comb[task]].ending_date);
}
}
}
free(Comb);
}
if (optionChosen == 4) {
int i;
int nrTasks;
int nrTasksGeral;
int *melhorAssignedTo; //Array que guarda a melhor combinação de atribuição de tasks
int **combinacoes; //Array de arrays que guarda todas as combinações binárias (cada array é uma combinação)
int **tarefasProgramador; //Array de arrays que guarda as tarefas que cada programador faz numa dada combinação
combinacoes=(int**)malloc(sizeof(int*)*pow(2,problem->T)); //Alocar espaço para o array de arrays 'combinacoes'. O espaço é 2^T porque existem 2^T combinações
for(int i=0;i<pow(2,problem->T);i++) //visto que cada task pode ou não ser feita
{
combinacoes[i]=(int*)malloc(sizeof(int)*problem->T);
}
 
tarefasProgramador=(int**)malloc(sizeof(int*)*problem->P); //Alocar espaço para o array de arrays 'tarefasProgramador'
for(int i=0;i<problem->P;i++)
{
tarefasProgramador[i]=(int*)malloc(sizeof(int)*problem->T);
}
 
melhorAssignedTo=(int*)malloc(sizeof(int)*problem->T); //Alocar espaço para o array 'melhorAssignedTo'
 
int n = problem->T; //Define a variável n com o número de tar
int arr[n]; //Inicializa o array 'arr' com n espaços
 
 
for(int i=0;i<pow(2,problem->T);i++) //Atribui o valor -1 a todas as posições do array de arrays 'combinacoes'
{
for(int k=0;k<problem->T;k++)
{
combinacoes[i][k]=-1;
}
}
gerarCombinacoes(n, arr, 0,combinacoes); //Chama a função que gera as combinações binárias
 
for(int i=0;i<problem->T;i++) //Inicializar o vetor melhorAssignedTo a -1
{
melhorAssignedTo[i]=-1;
}
 
nrTasksGeral=0; //Define-se a variável nrTasksGeral (que vai guardar o melhor número de tasks realizadas possível) a 0
for(int comb=0;comb<pow(2,problem->T);comb++) //Para cada combinação
{
 
for(int i=0;i<problem->P;i++) //Inicializar o vetor busy a -1
{
problem->busy[i]=-1;
}
 
for(int i=0;i<problem->P;i++) //Inicializar o vetor tarefasProgramador a -1
{
for(int k=0;k<problem->T;k++)
{
tarefasProgramador[i][k]=-1;
}
}
 
for(int i=0;i<problem->T;i++) //Inicializar o vetor assignedTo a -1
{
problem->task[i].assigned_to=-1;
}
 
nrTasks=0; //Variável nrTasks (que armazena o nr de tasks realizadas para cada combinação é inicializada a 0 para cada combinação)
 
for(int prog=0;prog<problem->P;prog++) //Para cada programador
{
for(int tar=0;tar<problem->T;tar++) //Para cada tarefa da combinação comb
{
                   
if(combinacoes[comb][tar]==1) //Caso a tarefa tar da combinacao comb possa ser feita
{
if(problem->busy[prog]==-1) //Caso o programador esteja disponível
{
if(problem->task[tar].assigned_to==-1) //Caso a tarefa não esteja atribuída
{
tarefasProgramador[prog][nrTasks]=tar; //Guarda-se o valor de tar em 'tarefasProgramador'
problem->busy[prog]=problem->task[tar].ending_date; //Define-se o programador busy até ao final dessa tarefa
problem->task[tar].assigned_to=prog; //Define-se que a tarefa tar está atribuída ao programador prog
nrTasks++; //Incrementa-se o número de tasks realizadas na combinação atual
}
}
 
else //Caso o programador esteja ocupado
{
if(problem->task[tar].assigned_to==-1) //Caso a tarefa não esteja atribuída
{
if(problem->busy[prog]<problem->task[tar].starting_date) //Se a starting date da tarefa for maior que o valor de busy (ending date da anterior)
{ //então o programador pode realizá-la porque não vai haver sobreposição
tarefasProgramador[prog][nrTasks]=tar; //Guarda-se o valor de tar em 'tarefasProgramador'
problem->busy[prog]=problem->task[tar].ending_date; //Define-se o programador busy até ao final dessa tarefa
problem->task[tar].assigned_to=prog; //Define-se que a tarefa tar está atribuída ao programador prog
nrTasks++; //Incrementa-se o número de tasks realizadas na combinação atual
}
}
}
}
}
}
int flagE=0; //A variável flagE vai servir como detetora de inviabilidades. É definida a zero aqui e vai passar por algumas condições.
//Caso o seu valor se mantenha a zero quer dizer que a combinação é viável. Caso o seu valor se altere para 1 quer dizer que
//a combinação não reune as condições necessárias para ser viável
 
//Para ser viável, todas as tasks que na combinação tenham o valor '1' têm que ser atribuídas. Caso haja tarefas que tenham o valor '1'
//na combinação mas que não tenham sido atribuídas, quer dizer que não há programadores suficientes para as realizar a todas, então
//a combinação revela-se inviável
 
for(int i=0;i<problem->T;i++) //Para cada elemento da combinacao
{
if(combinacoes[comb][i]==1) //Caso a task tenha que ser realizada
{
if(problem->task[i].assigned_to==-1) //Caso a task não tenha sido atribuída
{
flagE=1; //A combinação é inviável
break;
}
}
}
 
if(flagE==0) //Caso todas as tasks que tinham que ser feitas tiverem sido feitas
{
if(nrTasks>nrTasksGeral) //Se o número de tasks desta combinação for superior ao nr de tasks geral
{
for(int i=0;i<problem->T;i++) //Reicializar o vetor melhorAssignedTo a -1
{
melhorAssignedTo[i]=-1;
}
 
nrTasksGeral=nrTasks; //Atualiza-se o valor de nrTasksGeral para que contenha agora o melhor número de tasks
 
for(int i=0;i<problem->P;i++) //Para cada programador
{
for(int k=0;k<problem->T;k++) //Para cada tarefa
{
if(tarefasProgramador[i][k]!=-1) //Caso o elemento seja uma tarefa
{
melhorAssignedTo[tarefasProgramador[i][k]]=i; //Atribui ao melhorAssignedTo, na posição correspondente à tarefa 'tarefasProgramador[i][k]'
} //o valor de i (do programador)
}
}
}
}
}
for(int i=0;i<problem->T;i++) //No final de todas as combinações, copiamos o valor do array melhorAssignedTo para o array assignedTo do problema
{
problem->task[i].assigned_to=melhorAssignedTo[i];
}
 
//Agora imprimem-se os resultados no ficheiro
 
fprintf(fp, "----- Solução a ignorar os lucros! -----\n");
for(int p=0;p<problem->P;p++) //Para cada programador
{
fprintf(fp,"\nPara o Programador %d\n",(p+1));
for(int t=0;t<problem->T;t++) //Para cada tarefa
{
if(problem->task[t].assigned_to==p) //Imprimem-se, para cada p, os valores das tarefas atribuídas a este
{
fprintf(fp,"Foi atribuída a task que começa em %d e acaba em %d\n",problem->task[t].starting_date,problem->task[t].ending_date);
}
}
}
fprintf(fp,"\nForam feitas %d tarefas.\n",nrTasksGeral);
fprintf(fp,"------------------------------------\n");
}
if (optionChosen == 5) {
int *melhorAssignedTo; //Array que guarda a melhor combinação de atribuição de tasks
int **tarefasProgramador; //Array de arrays que guarda as tarefas que cada programador faz numa dada combinação
tarefasProgramador=(int**)malloc(sizeof(int*)*problem->P); //Alocar espaço para o array de arrays 'tarefasProgramador'
for(int i=0;i<problem->P;i++) { tarefasProgramador[i]=(int*)malloc(sizeof(int)*problem->T); }
 
melhorAssignedTo=(int*)malloc(sizeof(int)*problem->T); //Alocar espaço para o array 'melhorAssignedTo'
for(int i=0;i<problem->T;i++) { melhorAssignedTo[i]=-1; }
int n = problem->T; //Define a variável n com o número de tarefas
int arr[n]; //Inicializa o array 'arr' com n espaços
generateAllBinaryStrings(n, arr, 0, tarefasProgramador, melhorAssignedTo, problem); //Chama a função que gera as combinações binárias
 
for(int i=0;i<problem->T;i++) { //No final de todas as combinações, copiamos o valor do array melhorAssignedTo para o array assignedTo do problema
problem->task[i].assigned_to=melhorAssignedTo[i];
}
int nrTasks=0;
fprintf(fp, "----- Solução a ignorar os lucros! -----\n");
for(int p=0;p<problem->P;p++) {
fprintf(fp,"\nPROGRAMADOR %d\n",(p+1));
for(int t=0;t<problem->T;t++){
if(problem->task[t].assigned_to==p){
nrTasks++;
fprintf(fp,"Foi atribuída a task que começa em %d e acaba em %d\n",problem->task[t].starting_date,problem->task[t].ending_date);
}
}
}
fprintf(fp,"\nO número total de tarefas feitas é %d\n\n",nrTasks);
}
}
else {
if (optionChosen == 1) {
int i;
int nrTasks;
int nrTasksGeral;
int *melhorAssignedTo; //Array que guarda a melhor combinação de atribuição de tasks
int **combinacoes; //Array de arrays que guarda todas as combinações binárias (cada array é uma combinação)
int **tarefasProgramador; //Array de arrays que guarda as tarefas que cada programador faz numa dada combinação
combinacoes=(int**)malloc(sizeof(int*)*pow(2,problem->T)); //Alocar espaço para o array de arrays 'combinacoes'. O espaço é 2^T porque existem 2^T combinações
for(int i=0;i<pow(2,problem->T);i++) //visto que cada task pode ou não ser feita
{
combinacoes[i]=(int*)malloc(sizeof(int)*problem->T);
}
 
tarefasProgramador=(int**)malloc(sizeof(int*)*problem->P); //Alocar espaço para o array de arrays 'tarefasProgramador'
for(int i=0;i<problem->P;i++)
{
tarefasProgramador[i]=(int*)malloc(sizeof(int)*problem->T);
}
 
melhorAssignedTo=(int*)malloc(sizeof(int)*problem->T); //Alocar espaço para o array 'melhorAssignedTo'
                   
int n = problem->T; //Define a variável n com o número de tarefas
int arr[n]; //Inicializa o array 'arr' com n espaços
 
 
for(int i=0;i<pow(2,problem->T);i++) //Atribui o valor -1 a todas as posições do array de arrays 'combinacoes'
{
for(int k=0;k<problem->T;k++)
{
combinacoes[i][k]=-1;
}
}
gerarCombinacoes(n, arr, 0,combinacoes); //Chama a função que gera as combinações binárias
 
for(int i=0;i<problem->T;i++) //Inicializar o vetor melhorAssignedTo a -1
{
melhorAssignedTo[i]=-1;
}
 
nrTasksGeral=0; //Define-se a variável nrTasksGeral (que vai guardar o melhor número de tasks realizadas possível) a 0
int profitAtual; //Inicializa-se a variável profitAtual(que vai guardar o profit)
int profitGeral=0;
for(int comb=0;comb<pow(2,problem->T);comb++) //Para cada combinação
{
 
for(int i=0;i<problem->P;i++) //Inicializar o vetor busy a -1
{
problem->busy[i]=-1;
}
 
for(int i=0;i<problem->P;i++) //Inicializar o vetor tarefasProgramador a -1
{
for(int k=0;k<problem->T;k++)
{
tarefasProgramador[i][k]=-1;
}
}
 
for(int i=0;i<problem->T;i++) //Inicializar o vetor assignedTo a -1
{
problem->task[i].assigned_to=-1;
}
 
nrTasks=0;
profitAtual=0;
//printf("Para a combinacao %d\n",comb);
for(int prog=0;prog<problem->P;prog++) //Para cada programador
{
for(int tar=0;tar<problem->T;tar++)
{
if(combinacoes[comb][tar]==1) //Caso a tarefa tar da combinacao comb possa ser feita
{
if(problem->busy[prog]==-1) //Caso o programador esteja disponível
{
if(problem->task[tar].assigned_to==-1)
{
tarefasProgramador[prog][nrTasks]=tar;
problem->busy[prog]=problem->task[tar].ending_date;
problem->task[tar].assigned_to=prog;
nrTasks++;
profitAtual=profitAtual+problem->task[tar].profit;
//printf("A atribuir task %d ao programador %d\n",tar,prog);
}
}
 
else //Caso o programador esteja ocupado
{
if(problem->task[tar].assigned_to==-1)
{
if(problem->busy[prog]<problem->task[tar].starting_date)
{
tarefasProgramador[prog][nrTasks]=tar;
problem->busy[prog]=problem->task[tar].ending_date;
problem->task[tar].assigned_to=prog;
nrTasks++;
profitAtual=profitAtual+problem->task[tar].profit;
}
}
}
}
}
}
int flagE=0;
for(int i=0;i<problem->T;i++) //Para cada elemento da combinacao
{
if(combinacoes[comb][i]==1) //Caso a task tenha que ser realizada
{
if(problem->task[i].assigned_to==-1) //Caso a task não tenha sido atribuída
{
//printf("Combinação é inviável\n");
flagE=1;
break;
}
}
}
 
 
if(flagE==0) //Caso todas as tasks que tinham que ser feitas tiverem sido feitas
{
if(profitAtual>profitGeral)
{
for(int i=0;i<problem->T;i++) //Inicializar o vetor melhorAssignedTo a -1
{
melhorAssignedTo[i]=-1;
}
nrTasksGeral=nrTasks;
profitGeral=profitAtual;
for(int i=0;i<problem->P;i++)
{
for(int k=0;k<problem->T;k++)
{
if(tarefasProgramador[i][k]!=-1) //Caso o elemento seja uma tarefa
{
melhorAssignedTo[tarefasProgramador[i][k]]=i;
}
}
}
}
}
}
for(int i=0;i<problem->T;i++) //No final de todas as combinações, copiamos o valor do array melhorAssignedTo para o array assignedTo do problema
{
problem->task[i].assigned_to=melhorAssignedTo[i];
}
 
problem->total_profit=profitGeral; //Atu
 
fprintf(fp,"Solução com Lucros\n\n");
for(int p=0;p<problem->P;p++)
{
fprintf(fp,"\nPara o Programador %d\n",(p+1));
for(int t=0;t<problem->T;t++)
{
if(problem->task[t].assigned_to==p)
{
fprintf(fp,"Foi atribuída a task que começa em %d e acaba em %d com lucro de %d\n",problem->task[t].starting_date,problem->task[t].ending_date,problem->task[t].profit);
}
}
}
fprintf(fp,"\nForam feitas %d tarefas.\n",nrTasksGeral);
fprintf(fp,"O profit total é %d\n",problem->total_profit);
fprintf(fp,"------------------------------------\n");
}
if (optionChosen == 2) {
int *melhorAssignedTo; //Array que guarda a melhor combinação de atribuição de tasks
int **tarefasProgramador; //Array de arrays que guarda as tarefas que cada programador faz numa dada combinação
tarefasProgramador=(int**)malloc(sizeof(int*)*problem->P); //Alocar espaço para o array de arrays 'tarefasProgramador'
for(int i=0;i<problem->P;i++) { tarefasProgramador[i]=(int*)malloc(sizeof(int)*problem->T); }
 
melhorAssignedTo=(int*)malloc(sizeof(int)*problem->T); //Alocar espaço para o array 'melhorAssignedTo'
for(int i=0;i<problem->T;i++) { melhorAssignedTo[i]=-1; }
int n = problem->T; //Define a variável n com o número de tarefas
int arr[n]; //Inicializa o array 'arr' com n espaços
generateAllBinaryStrings(n, arr, 0, tarefasProgramador, melhorAssignedTo, problem); //Chama a função que gera as combinações binárias
 
for(int i=0;i<problem->T;i++) { //No final de todas as combinações, copiamos o valor do array melhorAssignedTo para o array assignedTo do problema
problem->task[i].assigned_to=melhorAssignedTo[i];
}
int nrTasks=0;
fprintf(fp, "----- Solução a contabilizar os lucros! -----\n");
for(int p=0;p<problem->P;p++) {
fprintf(fp,"\nPROGRAMADOR %d\n",(p+1));
for(int t=0;t<problem->T;t++){
if(problem->task[t].assigned_to==p){
fprintf(fp,"Foi atribuída a task que começa em %d e acaba em %d com lucro de %d\n",problem->task[t].starting_date,problem->task[t].ending_date,problem->task[t].profit);
}
}
}
fprintf(fp,"\nO profit total é %d\n\n",problem->total_profit);
}
}
//
// call your (recursive?) function to solve the problem here
problem->cpu_time = cpu_time() - problem->cpu_time;
printf("...Terminou\n");
//
// save solution data
//
fprintf(fp,"\n\n\n--------------------INFORMAÇÕES DE CONSULTA--------------------\n");
fprintf(fp,"NMec = %d\n",problem->NMec);
fprintf(fp,"T = %d\n",problem->T);
fprintf(fp,"P = %d\n",problem->P);
fprintf(fp,"Profits%s ignored\n",(problem->I == 0) ? " not" : "");
fprintf(fp,"Solution time = %.3e\n",problem->cpu_time);
printf("Solution time = %.3e\n",problem->cpu_time);
fprintf(fp,"%5s %15s %15s %10s" ,"Tasks", "Starting date", "Ending date","Profit\n");
#define TASK problem->task[i]
for(i = 0;i < problem->T;i++)
fprintf(fp,"%5d %15d %15d %10d\n",i, TASK.starting_date,TASK.ending_date,TASK.profit);
#undef TASK
//fprintf(fp,"End\n");
//
// terminate
//
if(fflush(fp) != 0 || ferror(fp) != 0 || fclose(fp) != 0) {
fprintf(stderr,"Error while writing data to file %s\n",problem->file_name);
exit(1);
}
}
#endif
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// main program
//
int main(int argc,char **argv) {
problem_t problem;
int NMec,T,P,I;
NMec = (argc < 2) ? 2020 : atoi(argv[1]);
T = (argc < 3) ? 5 : atoi(argv[2]);
P = (argc < 4) ? 2 : atoi(argv[3]);
I = (argc < 5) ? 0 : atoi(argv[4]);
if (I == 1) {
int option;
printf("Você escolheu ignorar os lucros! Temos 5 implementações que você poderá escolher!\n(1) SEGUNDA ABORDAGEM\n(2) TERCEIRA ABORDAGEM\n(3) QUARTA ABORDAGEM\n(4) QUINTA ABORDAGEM\n(5) SEXTA ABORDAGEM\nInsira um dos 5 números: \n");
scanf("%d", &option);
if ((option == 1) || (option == 2) || (option == 3) || (option == 4) || (option == 5)){
init_problem(NMec,T,P,I,&problem, option);
solve(&problem, option);
}
else {
printf("Opção inválida!");
return EXIT_FAILURE;
}
}
else if (I == 0) {
int option;
printf("Você escolheu não ignorar os lucros! Temos 2 implementações que você poderá escolher!\n(1) PRIMEIRA ABORDAGEM\n(2) SEGUNDA ABORDAGEM\nInsira um dos 3 números: \n");
scanf("%d", &option);
if ((option == 1) || (option == 2)){
init_problem(NMec,T,P,I,&problem, option);
solve(&problem, option);
}
else {
printf("Opção inválida!");
return EXIT_FAILURE;
}
}
else {
printf("O valor do I é inválido! Escolha 1 para ignorar os profits ou 0 para não ignorar os profits!\n");
}
return 0;
}

