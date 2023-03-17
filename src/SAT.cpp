#include"Suduku.h"
#include"Menu.h"
ALGraph G;
formula Formula;
char FileName[100],s[100];
int main()
{
	int op=1,op1,flag=0;
	while(op){
		Menu1();
		scanf("%d", &op);
		switch(op){
			case 0:
				break;
			case 1:
				op1=1;
				while(op1){
					Menu1_1();
					scanf("%d", &op1);
					switch(op1){
						case 0:
							break;
						case 1:
							Menu3();
							scanf("%d", &flag);
							if(flag){
								printf("请输入文件名:");
								scanf("%s",s);
								strcpy(FileName,s);
							}
							else{
								printf("请输入文件名:");
								scanf("%s", s);
								strcpy(FileName,"助教课设演示检查要求\\");
								strcat(FileName,s);
							}
							if(readfile(FileName,Formula,G)==OK)
								printf("读入文件成功!\n");
							else printf("读入文件失败!\n");
							printf("按任意键继续……");
							break;
						case 2:
							GraphPrint(G);
							printf("打印图成功!\n");
							printf("按任意键继续……");
							break;
						case 3:
							SAT_Solve(G,Formula);
							makefile(Formula,FileName);
							DestroyGraph(G);
							DestroyFormula(Formula);
							printf("按任意键继续……");
							break;
						default:
							printf("Please input number[0~3]\n");
					}
					if(!op1) break;
					getchar();getchar(); 
				}
				break;
			case 2:
				op1=1;
				while(op1){
					Menu1_2();
					int flag1=0; 
					scanf("%d", &op1);
					switch(op1){
						case 1:
							if(CreateUniqueMap(G,Formula,PlayMap,ChessMap,Hole)==OK){
								printf("创建棋盘成功!\n");
								flag1=1;
							}
							else printf("创建失败!\n"); 
							printf("按任意键继续……");
							break;
						case 2:
							PrintMap(PlayMap);
							printf("打印棋盘成功!\n");
							printf("按任意键继续……");
							break;
						case 3:
							if(!flag1){
								printf("还未创建棋盘!\n");
								printf("按任意键继续……");
								break;
							}
							Transform(G,Formula,ChessMap,Value);
							MakeCnfFile(G,Formula);
							if(DPLL(G,Formula,0)){
								AnswerMatch(Formula,ChessMap,Value);
							}
							ChessMapCpy(ChessMap,PlayMap);
							printf("按任意键继续……");
							break;
						case 4:
							Game(G,Formula,PlayMap,ChessMap,Value);
							printf("按任意键继续……");
							break;
						case 0:
							break;
						default:
							printf("Please input number[0~4]\n");
					}
					if(!op1) break;
					getchar();getchar();
				}
				break;
			default:
				printf("Please input number[0~2]\n");
		}
		if(!op1) continue;
		if(!op) break;
		getchar();getchar();
	}
} 