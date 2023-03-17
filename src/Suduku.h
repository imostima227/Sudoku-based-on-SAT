#include"SAT problem.h"
int ChessMap[10][10],PlayMap[10][10],Hole[10][10],Value[10][10][10];
char SAVE[1005][90];
void PrintChessMap(int ChessMap[][10])
{
	for(int i=1;i<=9;i++)
	{
		for(int j=1;j<=9;j++)
			printf("%d ",ChessMap[i][j]);
		printf("\n");
	}
}
void ValuePrint(int Value[][10][10])
{
	for(int i=1;i<=9;i++)
	{
		for(int j=1;j<=9;j++)
		{
			printf("%d %d:",i,j);
			for(int x=1;x<=9;x++)
				if(Value[i][j][x])
					printf("%d ",x);
			printf("\n");
		}
	}
}
status JudgeCorrect(int ChessMap[][10],int x,int n,int m)//n:行 m:列 
{
	//判断第n行 
	for(int j=1;j<=9;j++)
		if(ChessMap[n][j] == x) return ERROR;
	//判断第m列 
	for(int i=1;i<=9;i++)
		if(ChessMap[i][m] == x) return ERROR;
	//判断目标位置所在大方块
	int p=(n-1)/3*3+1,q=(m-1)/3*3+1;
	for(int i=p;i<p+3;i++)
	for(int j=q;j<q+3;j++)
		if(ChessMap[i][j] == x) return ERROR;
	return OK;
}
void CreateMap(int ChessMap[][10])
{
	memset(ChessMap,0,sizeof(int)*100);
	int i,j,x;
	srand((unsigned int)(time(NULL)));
	for(int k=0;k<17;k++)
	{
		i=rand()%9+1;
		j=rand()%9+1;
		x=rand()%9+1;
		if(!ChessMap[i][j] && JudgeCorrect(ChessMap,x,i,j))
			ChessMap[i][j]=x;
		else k--;
	}
}
void PrintMap(int ChessMap[][10])
{
	for(int i=1;i<=9;i++)
	{
		if(i==1 || i==4 || i==7){
			printf("|");
			for(int j=1;j<=20;j++) printf("-");
			printf("|\n");
		}
		printf("|");
		for(int j=1;j<=9;j++){
			if(ChessMap[i][j])
			printf("%d ",ChessMap[i][j]);
			else printf("_ ");
			if(j==3 || j==6 || j==9) printf("|");
		}
		printf("\n");
	}
	printf("|");
	for(int j=1;j<=20;j++) printf("-");
	printf("|\n");
}
void ChessMapCpy(int ChessMap[][10],int ChessMap_S[][10])
{
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
		ChessMap_S[i][j]=ChessMap[i][j];
} 
void ReadLiteral(ALGraph &G,formula &Formula,int x)
{
	int n=G.clause_Gcount;
	if(x){
		AddVertex(G,n,x);
		if(x>0)
			Formula.literal_frequency[2*x-1]++;
		else
			Formula.literal_frequency[-2*x]++;
	}
	else{
		G.clause_Gcount++;
		G.clause_max++;
	}
}
void LiteralMatch(formula &Formula,int ChessMap[][10],int Value[][10][10])//取值转化为文字
{
	int sq=1;//文字的序号 
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
		if(!ChessMap[i][j])
		for(int x=1;x<=9;x++)
			if(JudgeCorrect(ChessMap,x,i,j)==OK)
				Value[i][j][x]=sq++;
	Formula.literal_count=sq-1;
} 
void UnitRange(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//单格取值范围 
{
	int sign[10];//用来记录某个数字在本格是否能填
	memset(sign,0,sizeof(sign));
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
	{
		if(!ChessMap[i][j]){
			for(int x=1;x<=9;x++)
				if(JudgeCorrect(ChessMap,x,i,j))
					sign[x]=1;
			for(int x=1;x<=9;x++)
			if(sign[x]){
				for(int y=x+1;y<=9;y++)
				if(sign[y]){
					ReadLiteral(G,Formula,-Value[i][j][x]);
					ReadLiteral(G,Formula,-Value[i][j][y]);
					ReadLiteral(G,Formula,0); 
				}
				sign[x]=0;
			}	
		}
	}
}
void RowRange(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//行取值范围
{
	int sign[10];//记录数字在本行某列是否能填
	int arr[10];//记录本行需要补的数 
	memset(sign,0,sizeof(sign));
	for(int i=0;i<=9;i++) arr[i]=1;
	for(int i=1;i<=9;i++)
	{
		for(int j=1;j<=9;j++)
			if(ChessMap[i][j])
				arr[ChessMap[i][j]]=0;//标0表示本行不能补这个数 
		for(int x=1;x<=9;x++)
		{
			if(arr[x]){//x需要补 
				for(int j=1;j<=9;j++)
				if(!ChessMap[i][j] && JudgeCorrect(ChessMap,x,i,j))//x能够补进去 
					sign[j]=1;
				for(int j=1;j<=9;j++)
					if(sign[j]){
						for(int h=j+1;h<=9;h++)
						if(sign[h]){
							ReadLiteral(G,Formula,-Value[i][j][x]);
							ReadLiteral(G,Formula,-Value[i][h][x]);
							ReadLiteral(G,Formula,0);
						}
						sign[j]=0;//复原 
					}
			}
			arr[x]=1;//复原 
		}	
	}
}
void LineRange(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//列取值范围 
{
	int sign[10];
	int arr[10];
	memset(sign,0,sizeof(sign));
	for(int i=0;i<=9;i++) arr[i]=1;
	for(int j=1;j<=9;j++)
	{
		for(int i=1;i<=9;i++)
		if(ChessMap[i][j])
			arr[ChessMap[i][j]]=0;
		for(int x=1;x<=9;x++)
		{
			if(arr[x]){
				for(int i=1;i<=9;i++)
					if(!ChessMap[i][j] && JudgeCorrect(ChessMap,x,i,j))
						sign[i]=1;
				for(int i=1;i<=9;i++)
				{
					if(sign[i]){
						for(int h=i+1;h<=9;h++)
						if(sign[h]){
							ReadLiteral(G,Formula,-Value[i][j][x]);
							ReadLiteral(G,Formula,-Value[h][j][x]);
							ReadLiteral(G,Formula,0); 
						}
					}
					sign[i]=0;
				}
			}
			arr[x]=1;
		}
	}
}
void BlockRange(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//块取值范围
{
	int sign[10][10];
	int arr[10];
	memset(sign,0,sizeof(sign));
	for(int i=0;i<=9;i++) arr[i]=1; 
	for(int n=1;n<=9;n+=3)
		for(int m=1;m<=9;m+=3)
		{
			for(int i=n;i<n+3;i++)
				for(int j=m;j<m+3;j++)
					if(ChessMap[i][j])
						arr[ChessMap[i][j]]=0;
			for(int x=1;x<=9;x++)
			{
				if(arr[x]){
					for(int i=n;i<n+3;i++)
					for(int j=m;j<m+3;j++)
						if(!ChessMap[i][j] && JudgeCorrect(ChessMap,x,i,j))
							sign[i][j]=1;
					for(int i=n;i<n+3;i++)
					for(int j=m;j<m+3;j++)
						if(sign[i][j]){
							int i0=i,j0=j;
							 if(j0+1>m+2){
							 	j0=m;i0++;
							 }
							 else j0++;
							for(;i0<n+3;i0++)
							{
								for(;j0<m+3;j0++)
									if(sign[i0][j0]){
										ReadLiteral(G,Formula,-Value[i][j][x]);
										ReadLiteral(G,Formula,-Value[i0][j0][x]);
										ReadLiteral(G,Formula,0);
									}
								j0=m;
							}
							sign[i][j]=0;
						}
				}
				arr[x]=1;
			}
		}	
} 
void UnitEvalue(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//单格可能取值
{
	int sign[10];
	memset(sign,0,sizeof(sign));
	for(int i=1;i<=9;i++)
		for(int j=1;j<=9;j++)
		{
			if(!ChessMap[i][j]){
				for(int x=1;x<=9;x++)
				if(JudgeCorrect(ChessMap,x,i,j))
					sign[x]=1;
				int flag=0;
				for(int x=1;x<=9;x++)
				{
					if(sign[x]){
						ReadLiteral(G,Formula,Value[i][j][x]);
						flag=1;
					}
					sign[x]=0;
				}
				if(flag)
					ReadLiteral(G,Formula,0);
			}
				
		}
} 
void RowEvalue(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//行可能取值 
{
	int sign[10];
	int arr[10];
	memset(sign,0,sizeof(sign));
	for(int i=0;i<=9;i++) arr[i]=1;
	for(int i=1;i<=9;i++)
	{
		for(int j=1;j<=9;j++)
			if(ChessMap[i][j])
				arr[ChessMap[i][j]]=0;
		for(int x=1;x<=9;x++)
		{
			if(arr[x]){//x是本行要填的数 
				for(int j=1;j<=9;j++)
					if(!ChessMap[i][j] && JudgeCorrect(ChessMap,x,i,j))
						sign[j]=1;
				int flag=0;
				for(int j=1;j<=9;j++)
					if(sign[j]){
						ReadLiteral(G,Formula,Value[i][j][x]);
						flag=1;
						sign[j]=0;
					}
				if(flag)	
					ReadLiteral(G,Formula,0);
			}
			arr[x]=1;
		}
	}
}
void LineEvalue(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//列可能取值
{
	int sign[10];
	int arr[10];
	memset(sign,0,sizeof(sign));
	for(int i=0;i<=9;i++) arr[i]=1;
	for(int j=1;j<=9;j++)
	{
		for(int i=1;i<=9;i++)
			if(ChessMap[i][j])
				arr[ChessMap[i][j]]=0;
		for(int x=1;x<=9;x++)
		{
			if(arr[x]){
				for(int i=1;i<=9;i++)
					if(!ChessMap[i][j] && JudgeCorrect(ChessMap,x,i,j))
						sign[i]=1;
				int flag=0;
				for(int i=1;i<=9;i++)
				{
					if(sign[i]){
						ReadLiteral(G,Formula,Value[i][j][x]);
						flag=1;
						sign[i]=0;
					}
				}
				if(flag)
					ReadLiteral(G,Formula,0);
			}
			arr[x]=1;
		}
	}
} 
void BlockEvalue(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])//块可能取值
{
	int sign[10][10];
	int arr[10];
	memset(sign,0,sizeof(sign));
	for(int i=0;i<=9;i++) arr[i]=1;
	for(int n=1;n<=9;n+=3)
	{
		for(int m=1;m<=9;m+=3)
		{
			for(int i=n;i<n+3;i++)
			for(int j=m;j<m+3;j++)
				if(ChessMap[i][j])
					arr[ChessMap[i][j]]=0;
			for(int x=1;x<=9;x++)
			{
				if(arr[x]){
					for(int i=n;i<n+3;i++)
					for(int j=m;j<m+3;j++)
						if(!ChessMap[i][j] && JudgeCorrect(ChessMap,x,i,j))
						sign[i][j]=1;
					int flag=0;
					for(int i=n;i<n+3;i++)
					{
						for(int j=m;j<m+3;j++)
						if(sign[i][j]){
							ReadLiteral(G,Formula,Value[i][j][x]);
							flag=1;
							sign[i][j]=0;
						}
					}
					if(flag)
						ReadLiteral(G,Formula,0);
				}
				arr[x]=1;
			}
		}
	}	
} 
void AnswerMatch(formula &Formula,int ChessMap[][10],int Value[][10][10])//将答案反映到棋盘 
{
	for(int k=1;k<=Formula.literal_count;k++)
	{
		if(Formula.literal_tof[k]==1)
		for(int i=1;i<=9;i++)
			for(int j=1;j<=9;j++)
				for(int x=1;x<=9;x++)
					if(Value[i][j][x]==k)
						ChessMap[i][j]=x;
	}
}
void Transform(ALGraph &G,formula &Formula,int ChessMap[][10],int Value[][10][10])
{
	memset(Value,0,sizeof(int)*1000);
	LiteralMatch(Formula,ChessMap,Value);
	G.clause_Gcount=G.clause_max=1;
	G.clause_ini=6000; 
	InitialGraph(G);
	FormulaInitial(Formula);
	UnitRange(G,Formula,ChessMap,Value);
	RowRange(G,Formula,ChessMap,Value);
	LineRange(G,Formula,ChessMap,Value);
	BlockRange(G,Formula,ChessMap,Value);
	UnitEvalue(G,Formula,ChessMap,Value);
	RowEvalue(G,Formula,ChessMap,Value);
	LineEvalue(G,Formula,ChessMap,Value);
	BlockEvalue(G,Formula,ChessMap,Value);
	G.clause_Gcount--;
	G.clause_max--;
	Formula.clause_count=G.clause_Gcount;
	MatchFormula(G,Formula);
}
status JudgeUnique(int ChessMap[][10],int PlayMap[][10],int n,int m)//判断n行m列处是否有多解 
{
	ALGraph G;
	formula Formula;
	int value[10][10][10],num=0;
	memset(value,0,sizeof(value));
	LiteralMatch(Formula,PlayMap,value);
	for(int x=1;x<=9;x++)
		if(x!=ChessMap[n][m] && JudgeCorrect(PlayMap,x,n,m)){
			int save=PlayMap[n][m];
			PlayMap[n][m]=x;
			Transform(G,Formula,PlayMap,value);
			if(DPLL(G,Formula,0)==OK) 
			num++;
			if(num>0){
				PlayMap[n][m]=save;
				DestroyGraph(G);
				DestroyFormula(Formula);
				return FALSE;
			}
		}
	return TRUE;	
}
status JudgeEmpty(int Hole[][10])
{
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
		if(Hole[i][j]) return FALSE;
	return TRUE;
}
int SearchHole(int PlayMap[][10],int Hole[][10])
{
	int n,m;
	srand((unsigned int)(time(NULL)));
	n=rand()%9+1;
	m=rand()%9+1;
	if(JudgeEmpty(Hole)==TRUE) return 0; 
	while(!Hole[n][m]){
		n=rand()%9+1;
		m=rand()%9+1;
	}
	return n*10+m;
}
status DigHole(int n,int m,int ChessMap[][10],int PlayMap[][10],int Hole[][10],int &num)
{
	int hole_s[10][10],save=PlayMap[n][m];
	if(n==0 && m==0){
		srand((unsigned int)(time(NULL)));
		n=rand()%9+1;
		m=rand()%9+1; 
		if(DigHole(n,m,ChessMap,PlayMap,Hole,num)==OK)//初始位置 
			return OK;
	}
	if(num==0) return OK;//全部挖完 
	if(JudgeUnique(ChessMap,PlayMap,n,m)==TRUE){
		PlayMap[n][m]=0;
		Hole[n][m]=0;
		num--;
	}
	else return ERROR;
	ChessMapCpy(Hole,hole_s);
	int x=SearchHole(PlayMap,Hole);//寻找下一个洞 
	while(x){
		if(DigHole(x/10,x%10,ChessMap,PlayMap,Hole,num)==OK) return OK;
		else{
			Hole[x/10][x%10]=0;
			x=SearchHole(PlayMap,Hole);
		}
	}
	num++;
	PlayMap[n][m]=save;
	ChessMapCpy(hole_s,Hole);
	return ERROR;
}
status CreateUniqueMap(ALGraph &G,formula &Formula,int PlayMap[][10],int ChessMap[][10],int Hole[][10])
{
	int flag=1;
	while(flag){
		DestroyGraph(G);
		DestroyFormula(Formula);
		memset(PlayMap,0,sizeof(int)*100);
		memset(ChessMap,0,sizeof(int)*100);
		memset(Value,0,sizeof(int)*1000);
		memset(Hole,0,sizeof(int)*100);
		for(int i=1;i<=9;i++)
		for(int j=1;j<=9;j++)
			Hole[i][j]=1;
		CreateMap(ChessMap);
		Transform(G,Formula,ChessMap,Value);
		if(DPLL(G,Formula,0)==OK) flag=0;
	}
	AnswerMatch(Formula,ChessMap,Value);
	ChessMapCpy(ChessMap,PlayMap);
	int num;
	printf("请输入游戏需填入数字的个数[1~64]:");
	scanf("%d", &num);
	while(num<1 || num>64){
		printf("输入不符合规范，请重新输入!\n");
		scanf("%d", &num); 
	}
	DigHole(0,0,ChessMap,PlayMap,Hole,num);
	DestroyGraph(G);
	DestroyFormula(Formula);
	return TRUE;
}
void ReadMap(int ChessMap[][10],char SAVE[][90])
{
	int n,count=0;
	FILE *fp=fopen("suduku.txt","r");
	for(int i=1;i<=1000;i++)
		fscanf(fp,"%s",SAVE[i]);
	fclose(fp);
	printf("请选择要读入数独的序号:");
	scanf("%d", &n);
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
	{
		if(SAVE[n][count]=='.')
			ChessMap[i][j]=0;
		else ChessMap[i][j]=SAVE[n][count]-'0';
		count++;
	}
}
void GamePlay(int PlayMap[][10],int ChessMap[][10])
{
	int n,m,x,flag=1;
	int num=0;
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
		if(PlayMap[i][j])
			num++;
	int mark[10][10];
	memset(mark,0,sizeof(mark));
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
		if(PlayMap[i][j])
		mark[i][j]=1;
	int op=1;
	while(num<=81 && op){
		system("cls");
		PrintMap(PlayMap);
		printf("请选择操作:\n");
		printf("1.填入数字\n");
		printf("2.删除数字\n");
		printf("3.提示\n");
		printf("0.退出游戏\n");
		scanf("%d", &op);
		switch(op){
			case 1:
				printf("请选择行数，列数和填入的数字:");
				scanf("%d%d%d", &n, &m, &x);
				while((n<1||n>9) || (m<1||m>9) || (x<1 || x>9) || PlayMap[n][m] || JudgeCorrect(PlayMap,x,n,m)==ERROR){
					printf("输入不符合规范，请重新输入!\n");
					scanf("%d%d%d", &n, &m, &x);
				}
				PlayMap[n][m]=x;
				num++;
				break;
			case 2:
				printf("请选择行数，列数:");
				scanf("%d%d", &n, &m);
				while((n<1||n>9) || (m<1||m>9) || !ChessMap[n][m] || mark[n][m])
				{
					printf("输入不符合规范，请重新输入!\n");
					scanf("%d%d%d", &n, &m, &x);
				}
				PlayMap[n][m]=0;
				num--;
				break;
			case 3:
				printf("请输入行数和列数:");
				int i,j;
				scanf("%d%d", &i, &j);
				printf("%d",ChessMap[i][j]);
				break;
			case 0:
				break;
		}
		if(!op) break;
		getchar();getchar(); 
	}
	PrintMap(PlayMap);
	for(int i=1;i<=9;i++)
	for(int j=1;j<=9;j++)
		if(PlayMap[i][j]!=ChessMap[i][j]){
			flag=0;
			break;
		}
	if(flag==0){
		printf("结果错误！正解如下:\n");
		PrintMap(ChessMap);
	}
	else printf("结果正确！");
}
void Game(ALGraph &G,formula &Formula,int PlayMap[][10],int ChessMap[][10],int Value[][10][10])
{
	int op=1,i,j;
	int flag=0;
	while(op){
		memset(PlayMap,0,sizeof(int)*100);
		system("cls");system("cls");printf("\n\n");
		printf("-------------------------------\n");
		printf("        1.ReadMap\n");
		printf("        2.CreateMap\n");
		printf("        3.GameStart\n");
		printf("        4.PresentAnswer\n");
		printf("        0.exit\n");
		printf("-------------------------------\n");
		printf("请输入功能序号:");
		scanf("%d", &op);
		switch(op){
			case 1:
				memset(PlayMap,0,sizeof(int)*100);
				memset(ChessMap,0,sizeof(int)*100);
				memset(Value,0,sizeof(int)*1000);
				ReadMap(ChessMap,SAVE);
				flag=1;
				PrintMap(ChessMap); 
				ChessMapCpy(ChessMap,PlayMap);
				Transform(G,Formula,ChessMap,Value);
				if(DPLL(G,Formula,0)){
					AnswerMatch(Formula,ChessMap,Value);
				}
				printf("按任意键继续……");
				break;
			case 2:
				if(CreateUniqueMap(G,Formula,PlayMap,ChessMap,Hole)==OK){
					flag=1;
					printf("创建棋盘成功!\n");
				}
				else printf("创建棋盘失败!\n");
				printf("按任意键继续……");
				break;
			case 3:
				if(flag==0){
					printf("还未创建棋盘!\n");
					printf("按任意键继续……");
					break;
				}
				if(JudgeEmpty(PlayMap)==FALSE)
					GamePlay(PlayMap,ChessMap);
				flag=0;
				break;
			case 4:
				PrintMap(ChessMap);
				printf("按任意键继续……");
				break;
			case 0:
				break;
			default:
				printf("Please input number[0~5]\n");
		}
		if(!op) break;
		getchar();getchar();
	}
}
void MakeCnfFile(ALGraph G,formula Formula)
{
	FILE *fp=fopen("123.cnf","w");
	fprintf(fp,"p cnf %d %d\n",Formula.literal_count,G.clause_Gcount);
	for(int i=1;i<=G.clause_max;i++)
	{
		ArcNode *p=G.vertices[i].firstarc;
		do{
			fprintf(fp,"%d ",p->literal);
			p=p->nextarc;
		}while(p);
		fprintf(fp,"0\n");
	}
	fclose(fp);
}
