#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<math.h>
#include<time.h> 
#include"Graph & Formula.h"
//读取文件 
status readfile(char *FileName,formula &Formula,ALGraph &G)
{
	FILE *fp=fopen(FileName,"r");
	char c,s[500];
	while(1){
		c=fgetc(fp);
		if(c=='c')// 如果是注释 
			fgets(s,1000,fp);
		else if(c == 'p'){
			fscanf(fp,"%s",s);
			if(strcmp(s,"cnf")==0)
				break;
			else return ERROR;
		}
		else return ERROR;
	}
	fscanf(fp,"%d", &Formula.literal_count);
	fscanf(fp,"%d", &Formula.clause_count);
	//分配空间并初始化 
	FormulaInitial(Formula);
	//从文件中读取 
	G.clause_Gcount=Formula.clause_count;
	G.clause_max=G.clause_Gcount;
	G.clause_ini=G.clause_Gcount;
	InitialGraph(G);
	for(int i=1;i<=Formula.clause_count;i++){
		int literal=1;
		while(literal){
			fscanf(fp,"%d", &literal);
			if(literal>0){
				Formula.literal_frequency[2*literal-1]++;
				AddVertex(G,i,literal);
			}
			else if(literal<0){
				Formula.literal_frequency[-literal*2]++;
				AddVertex(G,i,literal);
			}
		}
	}
	MatchFormula(G,Formula);
	fclose(fp);
	return OK;
}
//生成res文件
status makefile(formula Formula,char *FileName) 
{
	int l=strlen(FileName),i,flag=0;
	for(i=0;i<l;i++)
	{
		if(FileName[i]=='.' && FileName[i+1]=='c' && FileName[i+2]=='n' && FileName[i+3]=='f'){
			flag=1;
			break;
		}	
	} 
	if(!flag) return ERROR;
	FileName[i+1]='r',FileName[i+2]='e',FileName[i+3]='s';
	FILE *fp=fopen(FileName,"w"); 
	if(Formula.ans==1){
		fprintf(fp,"s 1\nv ");
		for(int i=1;i<=Formula.literal_count;i++)
		if(Formula.literal_tof[i]==1) fprintf(fp,"%d ",i);
		else if(Formula.literal_tof[i]==0) fprintf(fp,"%d ",-i);
		fprintf(fp,"\nt %dms",Formula.time);
	}
	else if(Formula.ans==0){
		fprintf(fp,"s 0\n");
		fprintf(fp,"v\n"); 
		fprintf(fp,"t %dms",Formula.time);
	}
	else fprintf(fp,"s -1\nv ");
	fclose(fp);
	return OK;
}
//删除子句中的永真式
void Delete_Tautologies(ALGraph &G,formula &Formula)
{
	for(int i=1;i<=Formula.literal_count;i++)
	{
		save_node *p1,*p2;
		p1=Formula.save_true[i].p;
		if(!p1) continue;
		do{
			p2=Formula.save_false[i].p;
			if(!p2) break;
			do{
				if(p1->mark_clause->sequence == p2->mark_clause->sequence){
					DeleteClause(G,Formula,p1->mark_clause->sequence);
					p1->way=0;
					break;
				}
				p2=p2->next;
			}while(p2);
			p1=p1->next;
		}while(p1);
	}
}
//删除某一文字
void DeleteUnitartLiteral(ALGraph &G,formula &Formula,int literal)
{
	save_node *p;
	if(literal>0){
		Formula.literal_tof[literal]=1;
		p=Formula.save_true[literal].p;
		do{
			if(p->mark_clause->mark){
				DeleteClause(G,Formula,p->mark_clause->sequence);
				p->way=0;
			}
			p=p->next;
		}while(p);
	}
	else{
		Formula.literal_tof[-literal]=0;
		p=Formula.save_false[-literal].p;
		do{
			if(p->mark_clause->mark){
				DeleteClause(G,Formula,p->mark_clause->sequence);
				p->way=0;
			}
			p=p->next;
		}while(p);
	}
	DeleteLiteral(G,Formula,-literal); 
}
//恢复某一文字
void RestoreLiteral(ALGraph &G,formula &Formula,int literal)//literal表示被删除的文字 
{
	save_node *p;
	if(literal>0){
		//恢复被删除的子句 
		Formula.literal_tof[literal]=-1;
		p=Formula.save_true[literal].p;
		do{
			if(p->way==0){
				int n=p->mark_clause->sequence;//取该子句的序号 
				p->mark_clause->mark=1;
				p->way=-1; 
				G.clause_Gcount++;
				ArcNode *p1=G.vertices[n].firstarc;
				do{
					if(p1->mark){//该文字本身未被删除 
						G.vertices[n].literal_Gcount++;
					}
					p1=p1->nextarc;
				}while(p1);
			}
			p=p->next;
		}while(p);
		//恢复被删除的文字的反 
		p=Formula.save_false[literal].p;
		if(!p) return;
		do{
			if(p->mark_clause->mark && p->way==1){
				p->mark_clause->literal_Gcount++;
				p->way=-1; 
				p->node->mark=1;
			} 
			p=p->next;
		}while(p);
	}
	else{
		//恢复被删除的子句
		Formula.literal_tof[-literal]=-1;
		p=Formula.save_false[-literal].p;
		do{
			if(p->way==0){
				int n=p->mark_clause->sequence;//取该子句的序号
				p->mark_clause->mark=1;
				p->way=-1;
				G.clause_Gcount++;
				ArcNode *p1=G.vertices[n].firstarc;
				do{
					if(p1->mark){
						G.vertices[n].literal_Gcount++;
					}
					p1=p1->nextarc;
				}while(p1);
			}
			p=p->next;
		}while(p);
		//恢复被删除的文字的反 
		p=Formula.save_true[-literal].p;
		if(!p) return;
		do{
			if(p->mark_clause->mark && p->way==1){
				p->mark_clause->literal_Gcount++;
				p->way=-1;
				p->node->mark=1;
			} 
			p=p->next;
		}while(p);
	}	
} 
//判断是否有空子句
status JudgeEmptyClause(ALGraph G)
{
	for(int i=1;i<=G.clause_max;i++)
		if(G.vertices[i].mark && !G.vertices[i].literal_Gcount)
			return TRUE;
	return FALSE;
} 
//寻找本次操作的文字
int SearchLiteral(ALGraph G,formula &Formula,int &flag)
{
	int x;
	for(int i=1;i<=G.clause_max;i++)
	{
		if(G.vertices[i].mark && G.vertices[i].literal_Gcount==1){
			ArcNode *p=G.vertices[i].firstarc;
			do{
				if(p->mark){
					flag=1;
					return p->literal;
				}
				p=p->nextarc;
			}while(p);
		}
	}
	for(int i=1;i<=2*Formula.literal_count;i++)
	{
		int y=Formula.literal_sequence[i];
		y=y>0?y:-y;
		if(Formula.literal_tof[y]==-1)
			return Formula.literal_sequence[i];
	}
	return -1;
} 
//DPLL 
status DPLL(ALGraph &G,formula &Formula,int literal)
{ 
	int flag=0;
	if(literal){
		DeleteUnitartLiteral(G,Formula,literal);	
	}
	//GraphPrint(G);
	//Formula_Print(Formula);
	if(JudgeEmptyClause(G)==TRUE) return FALSE;
	if(!G.clause_Gcount) return TRUE;
	int x=SearchLiteral(G,Formula,flag);
	if(DPLL(G,Formula,x)==TRUE) return TRUE;
	else{
		RestoreLiteral(G,Formula,x);
		if(flag) return FALSE;
		//GraphPrint(G);
		//Formula_Print(Formula);
		if(DPLL(G,Formula,-x)==TRUE) return TRUE;
		else{
			RestoreLiteral(G,Formula,-x);
			//GraphPrint(G);
			//Formula_Print(Formula);
			return FALSE;
		}
	}
}
//解SAT问题
void SAT_Solve(ALGraph &G,formula &Formula)
{
	//删除重言式
	clock_t start,finish;
	start=clock();//开始运行 
	Delete_Tautologies(G,Formula);
	if(DPLL(G,Formula,0)==TRUE){
		printf("Satisfied!\n");
		Formula.ans=1;
		Literal_Print(Formula);
	}
	else{
		Formula.ans=0;
		printf("Unsatisfied!\n");
	}
	finish=clock();//结束运行
	Formula.time=(int)(1000*(finish-start)/CLOCKS_PER_SEC); 
	for(int i=1;i<=Formula.literal_count;i++)
		if(Formula.literal_tof[i]==-1) Formula.literal_tof[i]=1; 
	printf("函数运行时间：%dms\n",Formula.time);
} 