#include"define.h"
typedef struct ArcNode {         
	int literal;
	int mark;
    struct ArcNode  *nextarc;
} ArcNode;
typedef struct VNode{
    ArcNode *firstarc;      	
    int literal_Gcount;
    int mark;
    int sequence;//子句序号 
} VNode,*AdjList;
typedef  struct {  
    AdjList vertices;     	 
    int clause_Gcount; //邻接表中当前的子句数目 
    int clause_max;//子句最大数目 
    int clause_ini;//分配空间时用，主要针对数独 
} ALGraph;

typedef struct save_node{//文字对应的每个子句 
	ArcNode* node;//查找该文字在子句中是否被删除 
	VNode* mark_clause;//查找该子句是否被删除
	int way;//记录该记录删除的方式,0:整个子句删除 1:单个文字删除 
	save_node* next;
}save_node;
typedef struct save_form{//每个文字对应一个save 
	save_node* p;//子句的指针 
}save_form;
typedef struct formula{//记录邻接表中各种信息 
	int ans;//结果 
	int time;//运行时间 
	int clause_count;//子句的数目 
	int literal_count;//文字的数目  
	int* literal_frequency;//记录文字出现的频率（正负分别记录） 
	int* literal_tof;//记录文字目前的取值（1表示真，0表示假，-1表示未完成） 
	int* literal_sequence;//记录数据提取顺序 
	save_form *save_true;//正文字对应子句 
	save_form *save_false;//负文字对应子句 
}formula;
//功能函数 
void GraphPrint(ALGraph G);
void SequenceSort(formula &Formula);
void reset(int *s,int n,int x)//初始化数组 
{
	int max=n/4;
	for(int i=0;i<max;i++)
		s[i]=x;
}
void InitialGraph(ALGraph &G)//初始化邻接表 
{
	G.vertices=(VNode *)malloc((sizeof(VNode)+5)*G.clause_ini);
	for(int i=1;i<=G.clause_ini;i++)
	{
		G.vertices[i].firstarc=NULL;
		G.vertices[i].literal_Gcount=0;
		G.vertices[i].mark=1;
		G.vertices[i].sequence=i; 
	}
}
void DestroyGraph(ALGraph &G)//销毁邻接表
{
	if(G.clause_ini==0) return;
	if(G.vertices){
		free(G.vertices);
		G.vertices=NULL;
	}
	G.clause_ini=0;
	G.clause_max=0;
	G.clause_Gcount=0;	
} 
void AddVertex(ALGraph &G,int n,int literal)//向第n个子句添加文字 
{
	ArcNode *p,*q;
	p=(ArcNode *)malloc(sizeof(ArcNode));
	p->literal=literal,p->nextarc=NULL,p->mark=1;
	if(!G.vertices[n].literal_Gcount){
		G.vertices[n].firstarc=p;
		G.vertices[n].literal_Gcount++;
	}
	else{
		q=G.vertices[n].firstarc;
		while(q->nextarc){
			q=q->nextarc;
		}
		q->nextarc=p;
		G.vertices[n].literal_Gcount++;
	}
}
void DeleteClause(ALGraph &G,formula &Formula,int n)//删除子句 
{
	if(!G.vertices[n].mark) return;
	G.vertices[n].mark=0;
	G.vertices[n].literal_Gcount=0;
	G.clause_Gcount--;
}
void DeleteLiteral(ALGraph &G,formula &Formula,int literal)//删除文字 
{
	if(literal>0){
		save_node *p=Formula.save_true[literal].p;
		if(!p) return; 
		do{
			if(p->mark_clause->mark){
				p->way=1;
				p->node->mark=0;
				p->mark_clause->literal_Gcount--;
			}
			p=p->next;
		}while(p);
	}
	else{
		save_node *p=Formula.save_false[-literal].p;
		if(!p) return;
		do{
			if(p->mark_clause->mark){
				p->way=1;
				p->node->mark=0;
				p->mark_clause->literal_Gcount--;
			}
			p=p->next;
		}while(p);
	}
}
void GraphPrint(ALGraph G)//打印邻接表 
{
	for(int i=1;i<=G.clause_max;i++)
	{
		if(!G.vertices[i].mark) continue;
		printf("%d: ",i);
		ArcNode *p=G.vertices[i].firstarc;
		if(!p) continue;
		do{
			if(p->mark)
				printf("%d ",p->literal);
			p=p->nextarc;
		}while(p);
		printf("\n"); 
	}
}
int SearchLiteral_M(formula Formula)//寻找出现频率最高的文字 
{
	int max=0,x;
	for(int i=1;i<=2*Formula.literal_count;i++)
	{
		if(Formula.literal_frequency[i]>max){
			max=Formula.literal_frequency[i];
			if(i%2) x=(i+1)/2;
			else x=-i/2;
		}
	}
	return x;
}
//初始化Formula 
void FormulaInitial(formula &Formula)
{
	Formula.ans=-1;
	Formula.time=0;
	Formula.literal_frequency=(int *)malloc(sizeof(int)*(2*Formula.literal_count+10));
	Formula.literal_sequence=(int *)malloc(sizeof(int)*(2*Formula.literal_count+10));
	Formula.literal_tof=(int *)malloc(sizeof(int)*(Formula.literal_count+10));
	Formula.save_true=(save_form *)malloc(sizeof(save_form)*(Formula.literal_count+10));
	Formula.save_false=(save_form *)malloc(sizeof(save_form)*(Formula.literal_count+10));
	for(int i=0;i<=Formula.literal_count;i++)
	{
		Formula.save_true[i].p=NULL;
		Formula.save_false[i].p=NULL;
	}
	reset(Formula.literal_sequence,sizeof(int)*(2*Formula.literal_count+10),0);
	reset(Formula.literal_frequency,sizeof(int)*(2*Formula.literal_count+10),0);
	reset(Formula.literal_tof,sizeof(int)*(Formula.literal_count+10),-1);
}
void DestroyFormula(formula &Formula)
{
	if(Formula.literal_count == 0) return;
	if(Formula.literal_frequency){
		free(Formula.literal_frequency);
		Formula.literal_frequency=NULL;
	}
	if(Formula.literal_sequence){
		free(Formula.literal_sequence);
		Formula.literal_sequence=NULL;
	}
	if(Formula.literal_tof){
		free(Formula.literal_tof);
		Formula.literal_tof=NULL;
	}
	if(Formula.save_false){
		free(Formula.save_false);
		Formula.save_false=NULL;
	}
	if(Formula.save_true){
		free(Formula.save_true);
		Formula.save_true=NULL;
	}
}
void MatchFormula(ALGraph G,formula &Formula)
{
	for(int i=1;i<=G.clause_max;i++)
	{
		ArcNode *p=G.vertices[i].firstarc;
		do{
			save_node *ps1=(save_node *)malloc(sizeof(save_node));
			ps1->next=NULL,ps1->way=-1,ps1->mark_clause=&(G.vertices[i]);
			ps1->node=p;
			int literal=p->literal;
			if(literal>0){
				save_node *ps2=Formula.save_true[literal].p;
				if(!ps2) Formula.save_true[literal].p=ps1;
				else{
					while(ps2->next){
						ps2=ps2->next;
					}
					ps2->next=ps1;
				}
			}
			else{
				save_node *ps2=Formula.save_false[-literal].p;
				if(!ps2) Formula.save_false[-literal].p=ps1;
				else{
					while(ps2->next){
						ps2=ps2->next;
					}
					ps2->next=ps1;
				}
			}
			p=p->nextarc;
		}while(p);
	}
	SequenceSort(Formula);
}

void SequenceSort(formula &Formula)
{
	for(int i=1;i<=2*Formula.literal_count;i++)
	{
		int x=SearchLiteral_M(Formula);
		Formula.literal_sequence[i]=x;
		if(x>0){
			Formula.literal_frequency[2*x-1]=0;
			Formula.literal_frequency[2*x]=0;
		}
		else{
			Formula.literal_frequency[-2*x]=0;
			Formula.literal_frequency[-2*x-1]=0;
		}
	}
}
//显示每个文字的取值情况
void Literal_Print(formula Formula)
{
	for(int i=1;i<=Formula.literal_count;i++)
	{
		if(Formula.literal_tof[i]==1) printf("%d: True\n",i);
		else if(Formula.literal_tof[i]==0) printf("%d: False\n",i);
		else printf("%d: True\n",i); 
	}	
} 
//显示当前数据的记录情况 
void Formula_Print(formula Formula)
{
	for(int i=1;i<=Formula.literal_count;i++)
	{ 
		printf("%d: %d\n",i,Formula.literal_tof[i]);
		printf("   ");
		save_node *p1=Formula.save_true[i].p;
		save_node *p2=Formula.save_false[i].p;
		do{
			if(p1 && p1->mark_clause->mark && p1->node->mark){
				printf("%d ",p1->mark_clause->sequence);
			}
			if(p1)
				p1=p1->next;
		}while(p1);
		printf("\n   ");
		do{
			if(p2 &&p2->mark_clause->mark && p2->node->mark){
				printf("%d ",p2->mark_clause->sequence);
			}
			if(p2)
				p2=p2->next;
		}while(p2);
		printf("\n");	
	} 
}