/* ------------------------------------------------------ */
/*                      NGplay                            */
/*    An XBoard NegaScout Alpha/Beta Chess Engine         */
/*   ANSI C code compiles in Windows/Linux/Unix/AIX       */
/*                                                        */
/*  Features : NegaScout search, +LMR, +futility pruning  */
/*             iterative deepening, Null move heuristic,  */
/*             piece mobility + king safety evaluation,   */
/*             isolated + passed pawn evaluation,         */
/*             Basic Endgames (KQ,KR,KBB,KBN vs K)        */
/*                                                        */
/*         Author: George Georgopoulos (c) 2010-2013      */
/*         You are free to copy/derive from this code     */
/*         as long as you mention this copyright          */
/*         and keep the new code open source              */
/*                                                        */
/*    I should give credit to Tom Kerrigan and his TSCP   */
/* for inspiration about chess programming. Especially    */
/* his code for xboard  interface and book opening helped */
/* me a lot. However the main engine algorithm (search,   */
/* move generation and evaluation) was written completely */
/* from scratch.                                          */
/*    Also credit should be given to Bruce Moreland for   */
/* his excellent site which helped me a lot writing the   */
/* Principal Variation collection code.  thanks G.G.      */
/* ------------------------------------------------------ */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/timeb.h>
#include <math.h>

/* -------------------- HEADER -------------------------- */

#define Abs(a)            (((a) > 0) ? (a) : -(a))
#define SECONDS_PASSED    ((GetMillisecs() - start_time)/1000.0)
#define _NORMAL_OUTPUT    1
#define _XBOARD_OUTPUT    2
#define MAX_STACK         768
#define MAXMV             255
#define START_DEPTH       3
#define ADAPT_NULL_LIMIT  6
#define THREAT_DEPTH      2
#define MAX_DEPTH         48
#define IID_DEPTH         5
#define TACTICAL_MARGIN   0
#define LMR_MOVES         4
#define LMR_DEPTH_LIMIT   4
#define INFINITY_         10000
#define MATE_CUTOFF       9000
#define RESIGN_EVAL       950
#define TERMINAL_NODE     -1
#define white             1
#define black             10
#define none              3
#define LightSq           1
#define DarkSq            2
#define TwoColor          3
#define PAWN_V            100 
#define KNIGHT_V          320
#define BISHOP_V          325
#define ROOK_V            510
#define QUEEN_V           960
#define DELTAMARGIN       200
#define FUTIL_DEPTH       4
#define MByte             1048576
#define PV_CHANGE_THRESH  50
#define THREAT_THRESH     3
#define MAX_BOOK_MATCH    9999

enum {WPAWN=2,WKNIGHT,WBISHOP,WROOK,WQUEEN,WKING,BPAWN=12,BKNIGHT,BBISHOP,BROOK,BQUEEN,BKING,PIECEMAX};
int BishopSquareColor[2] ={DarkSq,LightSq};
int PieceValFromType[PIECEMAX]= {0, 0, PAWN_V, KNIGHT_V, BISHOP_V, ROOK_V, QUEEN_V, INFINITY_, 0, 0,
                                 0, 0, PAWN_V, KNIGHT_V, BISHOP_V, ROOK_V, QUEEN_V, INFINITY_ 
                                 };
int SignedMaterialT[PIECEMAX]=  {0, 0, PAWN_V,  KNIGHT_V,  BISHOP_V,  ROOK_V,  QUEEN_V, 0, 0, 0,
                                 0, 0, -PAWN_V, -KNIGHT_V, -BISHOP_V, -ROOK_V, -QUEEN_V, 0 
                                 };
int FutilityMargins[FUTIL_DEPTH] = {0, 300, 550, 900};
enum {NORMAL=0, CASTL, PROMOT};
enum {EXACT=1, CHECK_ALPHA, CHECK_BETA};
enum {CUT_NODE=0, PV_NODE};

typedef enum {
  A1=21, B1, C1, D1, E1, F1, G1, H1,
  A2=31, B2, C2, D2, E2, F2, G2, H2,
  A3=41, B3, C3, D3, E3, F3, G3, H3,
  A4=51, B4, C4, D4, E4, F4, G4, H4,
  A5=61, B5, C5, D5, E5, F5, G5, H5,
  A6=71, B6, C6, D6, E6, F6, G6, H6,
  A7=81, B7, C7, D7, E7, F7, G7, H7,
  A8=91, B8, C8, D8, E8, F8, G8, H8, ENDSQ
} squares;

struct mvdata {
  char flag;  /*0:NULL, 1:piece move, >1: pawn move  2=WPAWN or 12=BPAWN : simple pawn move, else stores promotion piece */
  char from;
  char to;
  char mvv_lva; /* stores value for move ordering. >0 captures or pawn promotion,  <0 non captures */
};

typedef union {
  struct mvdata m;
  int u;
} MOVE;

typedef struct LINE {
  int cmove;                 /* Number of moves in the line.*/
  MOVE argmove[MAX_DEPTH+2]; /* The line.                   */
} LINE;

typedef struct piece_st {
  int type;
  int xy;
  int mobility; /* for pieces : number of moves - max_per piece/2 , for pawns: passed pawn evaluation */
  struct piece_st *next;
  struct piece_st *prev;
} PIECE;

/* ---------- TRANSPOSITION TABLE DEFINITIONS ------------- */

struct tt_st {
  MOVE hmove;
  char flag;
  char depth;
  int value;
  unsigned int PositionHashUpper;
} *T_T, *Opp_T_T;

struct ptt_st {
  int value;
  unsigned long long PawnHash;
} *P_T_T;

unsigned int MAX_TT, PMAX_TT;

/* -------------------- GLOBALS ------------------------- */

PIECE Wpieces[16], Bpieces[16], empty_p={0,0,0,NULL,NULL},  fence_p={-1,-1,-1,NULL,NULL};

PIECE *board[120] = { &fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,
                      &fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&empty_p,&fence_p,
                      &fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,
                      &fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p,&fence_p
                    };

int boardXY[120] ={-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
                   -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
                   -1, 0, 1, 2, 3, 4, 5, 6, 7,-1,
                   -1, 8, 9,10,11,12,13,14,15,-1,
                   -1,16,17,18,19,20,21,22,23,-1,
                   -1,24,25,26,27,28,29,30,31,-1,
                   -1,32,33,34,35,36,37,38,39,-1,
                   -1,40,41,42,43,44,45,46,47,-1,
                   -1,48,49,50,51,52,53,54,55,-1,
                   -1,56,57,58,59,60,61,62,63,-1,
                   -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
                   -1,-1,-1,-1,-1,-1,-1,-1,-1,-1};

int board64[64] = {A1, B1, C1, D1, E1, F1, G1, H1,
                   A2, B2, C2, D2, E2, F2, G2, H2,
                   A3, B3, C3, D3, E3, F3, G3, H3,
                   A4, B4, C4, D4, E4, F4, G4, H4,
                   A5, B5, C5, D5, E5, F5, G5, H5,
                   A6, B6, C6, D6, E6, F6, G6, H6,
                   A7, B7, C7, D7, E7, F7, G7, H7,
                   A8, B8, C8, D8, E8, F8, G8, H8};

int RowNum[120] ={0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,1,1,1,1,1,1,1,1,0,
                  0,2,2,2,2,2,2,2,2,0,
                  0,3,3,3,3,3,3,3,3,0,
                  0,4,4,4,4,4,4,4,4,0,
                  0,5,5,5,5,5,5,5,5,0,
                  0,6,6,6,6,6,6,6,6,0,
                  0,7,7,7,7,7,7,7,7,0,
                  0,8,8,8,8,8,8,8,8,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0};

int ColNum[120] ={0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,1,2,3,4,5,6,7,8,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0};


int Central[120]={0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,1,1,0,0,0,0,
                  0,0,0,0,1,1,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0};

int PartCen[120]={0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,1,1,1,1,0,0,0,
                  0,0,0,1,0,0,1,0,0,0,
                  0,0,0,1,0,0,1,0,0,0,
                  0,0,0,1,1,1,1,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0};

int WhiteSq[120]={0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,1,0,1,0,1,0,1,0,
                  0,1,0,1,0,1,0,1,0,0,
                  0,0,1,0,1,0,1,0,1,0,
                  0,1,0,1,0,1,0,1,0,0,
                  0,0,1,0,1,0,1,0,1,0,
                  0,1,0,1,0,1,0,1,0,0,
                  0,0,1,0,1,0,1,0,1,0,
                  0,1,0,1,0,1,0,1,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0};

int PartEdg[120]={0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,1,1,1,1,1,1,0,0,
                  0,0,1,0,0,0,0,1,0,0,
                  0,0,1,0,0,0,0,1,0,0,
                  0,0,1,0,0,0,0,1,0,0,
                  0,0,1,0,0,0,0,1,0,0,
                  0,0,1,1,1,1,1,1,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0};

int Edge[120]=   {0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,1,1,1,1,1,1,1,1,0,
                  0,1,0,0,0,0,0,0,1,0,
                  0,1,0,0,0,0,0,0,1,0,
                  0,1,0,0,0,0,0,0,1,0,
                  0,1,0,0,0,0,0,0,1,0,
                  0,1,0,0,0,0,0,0,1,0,
                  0,1,0,0,0,0,0,0,1,0,
                  0,1,1,1,1,1,1,1,1,0,
                  0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,0,0,0,0,0,0};

int KnightE[120]={0, 0, 0, 0, 0, 0, 0, 0, 0,0,
                  0, 0, 0, 0, 0, 0, 0, 0, 0,0,
                  0,-4,-4,-4,-4,-4,-4,-4,-4,0,
                  0,-4, 0, 0, 0, 0, 0, 0,-4,0,
                  0,-4, 0, 2, 2, 2, 2, 0,-4,0,
                  0,-4, 0, 2, 4, 4, 2, 0,-4,0,
                  0,-4, 0, 2, 4, 4, 2, 0,-4,0,
                  0,-4, 0, 2, 2, 2, 2, 0,-4,0,
                  0,-4, 0, 0, 0, 0, 0, 0,-4,0,
                  0,-4,-4,-4,-4,-4,-4,-4,-4,0,
                  0, 0, 0, 0, 0, 0, 0, 0, 0,0,
                  0, 0, 0, 0, 0, 0, 0, 0, 0,0};

int W_Pawn_E[120], B_Pawn_E[120];

int wking=E1, bking=E8; 
int EnPassantSq=0;
int gflags = 0;  /* bit 0  wkmoved    sample code:  if (xy1==E1) gflags |= 1;
                    bit 1  wra1moved     >>         if (xy1==A1) gflags |= 2; 
                    bit 2  wrh1moved     >>         if (xy1==H1) gflags |= 4;
                    bit 3  bkmoved       >>         if (xy1==E8) gflags |= 8; 
                    bit 4  bra8moved     >>         if (xy1==A8) gflags |= 16; 
                    bit 5  brh8moved     >>         if (xy1==H8) gflags |= 32; 
                    bit 6  WHasCastled   >>         if (xy2==G1 || xy2==C1) gflags |= 64; 
                    bit 7  BHasCastled   >>         if (xy2==G8 || xy2==C8) gflags |= 128; 
                    bit 8  Side to move, black has moved bit set   --> gflags |= 256;
                                         white has moved bit reset --> gflags &= ~256;
                 */

unsigned long long hash_board[PIECEMAX][ENDSQ];
unsigned long long hash_ep[64];

/* side to move, kings, rooks, en passant status stack */
struct cst {
  int flags; /* see gflags above */
  int EpSquare;
} cstack[MAX_STACK];  

int cst_p=0;

struct mvst {
  MOVE move;
  PIECE *captured;
  int capt;
  int special;   /* values: NORMAL,CASTL,PROMOT */
  unsigned long long PositionHash;
  unsigned long long PawnHash;
  int material;
} move_stack[MAX_STACK];  

int mv_stack_p=0;

int side=white;

int max_time = 180*1000; /* default level 3 minutes / move ---> 40 moves in 2 hours */
int start_time, stop_time;

int NotStartingPosition=0;
int nodes;
int Starting_Mv;

int ComputerSide = black; 
int HalfMovesPlayed=0, FiftyMoves=0, Xoutput=0;

FILE *book_file=NULL;
char CurrentLine[2048] = {'\0','\0'};
int MatchingBookMoves[MAX_BOOK_MATCH];

int Pieces=0;
int LoneKingReachedEdge=0;

unsigned long long Rnext = 1;

LINE GlobalPV;
MOVE PlayerMove;

int TimeIsUp, ngmax=-INFINITY_, PrevNgmax=-INFINITY_, danger;
int NofCores;

int W_history[6][ENDSQ], B_history[6][ENDSQ];
int W_Killers[2][MAX_DEPTH], B_Killers[2][MAX_DEPTH];

/* -------------- UTILITY FUNCTIONS ---------------------------------- */

void Init_Pawn_Eval(void)
{
  int i, xy, ret;
  for (i=0; i<120; i++) {
    W_Pawn_E[i] = B_Pawn_E[i] = 0;
  }
  for (i=0; i<64; i++) {
    xy = board64[i];
    ret=0;
    if ((xy==D2) || (xy==E2)) ret -= 8;
    if ((xy==C2)) ret -= 6;
    if ((xy==D4) || (xy==E4)|| (xy==C4)) ret += 2;
    if (xy >= A5) ret += 2;
    if (xy >= A6) ret += 5;
    if (xy >= A7) ret += 20;         
    W_Pawn_E[xy] = ret;
    ret=0;
    if ((xy==D7) || (xy==E7)) ret += 8;
    if ((xy==C7)) ret += 6;
    if ((xy==D5) || (xy==E5) || (xy==C5)) ret -= 2;
    if (xy<=H4) ret -= 2;
    if (xy<=H3) ret -= 5;
    if (xy<=H2) ret -= 20;         
    B_Pawn_E[xy] = ret;
  }
}

void ResetHistory(void)
{
  register int d,i;
  for (d=0; d<6; d++) { 
    for (i=A1; i<ENDSQ; i++) {
      W_history[d][i] = 0;
      B_history[d][i] = 0;
    }
  }
  for (i=0; i<2; i++) {
    for (d=0; d<MAX_DEPTH; d++) {
      W_Killers[i][d] = 0;
      B_Killers[i][d] = 0;
    }
  }
}

void InitPieces(void)
{
  int i;
  Wpieces[0].type = WKING; 
  Wpieces[0].xy   = 0;
  Wpieces[0].mobility = 0;
  Wpieces[0].next = &Wpieces[1];
  Wpieces[0].prev = NULL;

  Wpieces[1].type = WQUEEN;
  Wpieces[1].xy   = 0;
  Wpieces[1].mobility = 0;
  Wpieces[1].next = &Wpieces[2];
  Wpieces[1].prev = &Wpieces[0];

  Wpieces[2].type = WROOK;
  Wpieces[2].xy   = 0;
  Wpieces[2].mobility = 0;
  Wpieces[2].next = &Wpieces[3];
  Wpieces[2].prev = &Wpieces[1];

  Wpieces[3].type = WROOK;
  Wpieces[3].xy   = 0;
  Wpieces[3].mobility = 0;
  Wpieces[3].next = &Wpieces[4];
  Wpieces[3].prev = &Wpieces[2];

  Wpieces[4].type = WBISHOP;
  Wpieces[4].xy   = 0;
  Wpieces[4].mobility = 0;
  Wpieces[4].next = &Wpieces[5];
  Wpieces[4].prev = &Wpieces[3];

  Wpieces[5].type = WBISHOP;
  Wpieces[5].xy   = 0;
  Wpieces[5].mobility = 0;
  Wpieces[5].next = &Wpieces[6];
  Wpieces[5].prev = &Wpieces[4];

  Wpieces[6].type = WKNIGHT;
  Wpieces[6].xy   = 0;
  Wpieces[6].mobility = 0;
  Wpieces[6].next = &Wpieces[7];
  Wpieces[6].prev = &Wpieces[5];

  Wpieces[7].type = WKNIGHT;
  Wpieces[7].xy   = 0;
  Wpieces[7].mobility = 0;
  Wpieces[7].next = &Wpieces[8];
  Wpieces[7].prev = &Wpieces[6];

  for (i=8; i<16; i++) {
    Wpieces[i].type = WPAWN;
    Wpieces[i].xy   = 0;
    Wpieces[i].mobility = 0;
    if (i==15) {
      Wpieces[i].next = NULL;
    } else {
      Wpieces[i].next = &Wpieces[i+1];
    }
    Wpieces[i].prev = &Wpieces[i-1];
  }
  
  Bpieces[0].type = BKING;
  Bpieces[0].xy   = 0;
  Bpieces[0].mobility = 0;
  Bpieces[0].next = &Bpieces[1];
  Bpieces[0].prev = NULL;

  Bpieces[1].type = BQUEEN;
  Bpieces[1].xy   = 0;
  Bpieces[1].mobility = 0;
  Bpieces[1].next = &Bpieces[2];
  Bpieces[1].prev = &Bpieces[0];

  Bpieces[2].type = BROOK;
  Bpieces[2].xy   = 0;
  Bpieces[2].mobility = 0;
  Bpieces[2].next = &Bpieces[3];
  Bpieces[2].prev = &Bpieces[1];

  Bpieces[3].type = BROOK;
  Bpieces[3].xy   = 0;
  Bpieces[3].mobility = 0;
  Bpieces[3].next = &Bpieces[4];
  Bpieces[3].prev = &Bpieces[2];

  Bpieces[4].type = BBISHOP;
  Bpieces[4].xy   = 0;
  Bpieces[4].mobility = 0;
  Bpieces[4].next = &Bpieces[5];
  Bpieces[4].prev = &Bpieces[3];

  Bpieces[5].type = BBISHOP;
  Bpieces[5].xy   = 0;
  Bpieces[5].mobility = 0;
  Bpieces[5].next = &Bpieces[6];
  Bpieces[5].prev = &Bpieces[4];

  Bpieces[6].type = BKNIGHT;
  Bpieces[6].xy   = 0;
  Bpieces[6].mobility = 0;
  Bpieces[6].next = &Bpieces[7];
  Bpieces[6].prev = &Bpieces[5];

  Bpieces[7].type = BKNIGHT;
  Bpieces[7].xy   = 0;
  Bpieces[7].mobility = 0;
  Bpieces[7].next = &Bpieces[8];
  Bpieces[7].prev = &Bpieces[6];

  for (i=8; i<16; i++) {
    Bpieces[i].type = BPAWN;
    Bpieces[i].xy   = 0;
    Bpieces[i].mobility = 0;
    if (i==15) {
      Bpieces[i].next = NULL;
    } else {
      Bpieces[i].next = &Bpieces[i+1];
    }
    Bpieces[i].prev = &Bpieces[i-1];
  }
}

int GetMillisecs(void)
{
  struct timeb timebuffer;
  ftime(&timebuffer);
  return (timebuffer.time * 1000) + timebuffer.millitm;
}

int NextSide(int color)
{
  if (color==white) {
    return black;
  } else {
    return white;
  }
}

void ExitErrorMesg(const char *msg)
{
  fprintf(stderr,"\n\n%s\n\n",msg);
  exit(1);
}

void EmptyBoard(void)
{
  register int i;
  InitPieces();
  for (i=0; i<64; i++) {
    board[board64[i]]=&empty_p;
  }
  ResetHistory();
}

/* ------------ RANDOM NUMBERS / HASH HANDLING ---------------------------------- */

#define MTlength 624
static const unsigned int bitMask_32=0xffffffff;
static const unsigned int bitPow_31=1<<31;
unsigned int mt[MTlength];
unsigned int idx=0;

void InitRand32_MT(unsigned int seed)
{
  unsigned int i;
  idx=0;
  mt[0]=seed;
  for(i=1;i<MTlength;i++) mt[i]=(1812433253*(mt[i-1]^(mt[i-1]>>30))+i)&bitMask_32;
}

unsigned long long GetRandom32_MT(void)
{
  unsigned int y,i;
  if(idx==0) {
    for(i=0;i<MTlength;i++){
      y=(mt[i]&bitPow_31)+(mt[(i+1)%MTlength]&(bitPow_31-1));
      mt[i]=mt[(i+397)%MTlength]^(y>>1);
      if(y%2) mt[i]^=2567483615;
    }
  }
  y=mt[idx];
  y^= y>>11;
  y^=(y<< 7)&2636928640;
  y^=(y<<15)&4022730752;
  y^= y>>18;
  idx=(idx+1)%MTlength;
  return y;
}

unsigned long long GetRandom64_MT(void)
{
  unsigned long long ret;
  unsigned int high, low;
  
  low  = GetRandom32_MT();
  high = GetRandom32_MT();
  
  ret = (unsigned long long) high << 32 | low;

  return ret;
}

void InitHash(void)
{
  int i, j;
  InitRand32_MT(3571);

  for (i = 0; i < PIECEMAX; ++i) {
    for (j = 0; j < ENDSQ; ++j) {
      hash_board[i][j] = GetRandom64_MT(); 
    }
  }
  for (i = 0; i < 64; ++i) {
    hash_ep[i] = GetRandom64_MT();
  }
}

unsigned long long GetPositionHash(unsigned long long *pawn_hash)
{
  unsigned long long ret;
  if (mv_stack_p==1) {
    register int i;
    ret = (*pawn_hash) = move_stack[mv_stack_p].material = 0;  
    for (i=0; i<16; i++) {
      if (Wpieces[i].xy) {
        move_stack[mv_stack_p].material += SignedMaterialT[Wpieces[i].type];
        if (Wpieces[i].type == WPAWN) {
          (*pawn_hash) ^= hash_board[ WPAWN ][Wpieces[i].xy];
        }
        ret ^= hash_board[ Wpieces[i].type ][Wpieces[i].xy];
      }
      if (Bpieces[i].xy) {
        move_stack[mv_stack_p].material += SignedMaterialT[Bpieces[i].type];
        if (Bpieces[i].type == BPAWN) {
          (*pawn_hash) ^= hash_board[ BPAWN ][Bpieces[i].xy];
        }
        ret ^= hash_board[ Bpieces[i].type ][Bpieces[i].xy];
      }
    }
    if (EnPassantSq) {
      ret ^= hash_ep[boardXY[EnPassantSq]];
    }
    ret ^= (gflags & 319);
  } else {
    register int prevmovstp, xy1, xy2, ptype;
    register struct mvst* p;
    register struct cst* cp;

    prevmovstp=mv_stack_p-1;
    p  = &move_stack[mv_stack_p];
    cp = &cstack[mv_stack_p];
    xy1=p->move.m.from;
    xy2=p->move.m.to;
    ret = (move_stack[prevmovstp].PositionHash);
    (*pawn_hash) = (move_stack[prevmovstp].PawnHash);
    ptype = board[xy2]->type;
    p->material = move_stack[prevmovstp].material;

    if (p->special == NORMAL) {
      ret ^= hash_board[ ptype ][xy1];
      if (ptype==WPAWN || ptype==BPAWN) {
        (*pawn_hash) ^= hash_board[ ptype ][xy1];
      }
    } else if (p->special == PROMOT) {
      p->material += SignedMaterialT[ptype];
      if (ptype>black) {
        p->material += PAWN_V;
        ret ^= hash_board[ BPAWN ][xy1];
        (*pawn_hash) ^= hash_board[ BPAWN ][xy1];
      } else {
        p->material -= PAWN_V;
        ret ^= hash_board[ WPAWN ][xy1];
        (*pawn_hash) ^= hash_board[ WPAWN ][xy1];
      }
    } else if (p->special == CASTL) {
      ret ^= hash_board[ ptype ][xy1];
      if (xy2==G1) {
        ret ^= hash_board[ WROOK ][H1];
        ret ^= hash_board[ WROOK ][F1];
      } else if (xy2==C1) {
        ret ^= hash_board[ WROOK ][A1];
        ret ^= hash_board[ WROOK ][D1];
      } else if (xy2==G8) {
        ret ^= hash_board[ BROOK ][H8];
        ret ^= hash_board[ BROOK ][F8];
      } else if (xy2==C8) {
        ret ^= hash_board[ BROOK ][A8];
        ret ^= hash_board[ BROOK ][D8];
      }
    } 
    ret ^= hash_board[ ptype ][xy2];
    if (ptype==WPAWN || ptype==BPAWN) {
      (*pawn_hash) ^= hash_board[ ptype ][xy2];
    }
    ptype = p->captured->type;
    if (ptype) {
      p->material -= SignedMaterialT[ptype];
      ret ^= hash_board[ ptype ][p->capt]; 
      if (ptype==WPAWN || ptype==BPAWN) {
        (*pawn_hash) ^= hash_board[ ptype ][p->capt];
      }
    }
    if (cp->EpSquare) {
      ret ^= hash_ep[boardXY[cp->EpSquare]];
    }
    if (EnPassantSq) {
      ret ^= hash_ep[boardXY[EnPassantSq]];
    }
    ret ^= (cp->flags & 319);
    ret ^= (gflags & 319);
  }
  return ret;
}

int CheckForDraw(void)
{
  register int i;
  unsigned long long hashP = move_stack[mv_stack_p].PositionHash;
  register struct mvst* p;
  for (i = mv_stack_p-2; i > 0; i-=2) {
    p = &move_stack[i];
    if (p->captured->type /* capture */ || p->move.m.flag>1 /* pawn move */) {
      return 0;
    }
    if (hashP == p->PositionHash) {
      return 1;
    }
  }
  return 0;
}

int HashRepetitions(void)
{
  int i;
  int ret = 0;
  unsigned long long hashP = move_stack[mv_stack_p].PositionHash;
  for (i = 1; i < mv_stack_p; ++i) {
    if (hashP == move_stack[i].PositionHash)
      ++ret;
  }
  return ret;
}

/* ------------------- TRANSPOSITION TABLE ROUTINES ---------------------------------- */
#define CLUSTER_SIZE 2

int Check_TT_PV(struct tt_st *tt, int pdepth, unsigned long long PosHash, int *valueP, MOVE* hmvp)
{
  register unsigned int Indx;
  register int lflag, ldepth, lvalue, i;
  register struct tt_st * ttentry;
  unsigned int key32 = PosHash >> 32;

  Indx = PosHash & MAX_TT;
  ttentry = &(tt[Indx]);
  for (i=0; i<CLUSTER_SIZE; i++) {
    if (ttentry->PositionHashUpper == key32) { //hit
      ldepth = ttentry->depth;
      if (ttentry->hmove.u) {
        *hmvp  = ttentry->hmove;
      }
      if (ldepth >= pdepth) {
        lflag  = ttentry->flag;
        lvalue = ttentry->value;
        if (lflag==EXACT) {
          *valueP = lvalue;
          return 1;
        }
      }
    }
    ttentry++;
  }
  return 0;
}

int Check_TT(struct tt_st *tt, int alpha, int beta, int pdepth, unsigned long long PosHash, int *valueP, MOVE* hmvp)
{
  register unsigned int Indx;
  register int lflag, ldepth, lvalue, i;
  register struct tt_st * ttentry;
  unsigned int key32 = PosHash >> 32;

  Indx = PosHash & MAX_TT;
  ttentry = &(tt[Indx]);
  for (i=0; i<CLUSTER_SIZE; i++) {
    if (ttentry->PositionHashUpper == key32) { //hit
      ldepth = ttentry->depth;
      if (ttentry->hmove.u) {
        *hmvp  = ttentry->hmove;
      }
      if (ldepth >= pdepth) {
        lflag  = ttentry->flag;
        lvalue = ttentry->value;
        switch (lflag) {
          case CHECK_ALPHA:  
            if (lvalue <= alpha) {
              *valueP = alpha;
              return 1;
            }
          break;
          case CHECK_BETA:
            if (lvalue >= beta) {
              *valueP = beta;
              return 1;
            }
          break;
          case EXACT:
          *valueP = lvalue;
          return 1;
        }
      }
    }
    ttentry++;
  }
  return 0;
}

void Update_TT(struct tt_st *tt, int pdepth, int pvalue, int pflag, unsigned long long PosHash, MOVE hmv)
{
  register unsigned int Indx;
  register struct tt_st *tupd;
  unsigned int key32 = PosHash >> 32;
  Indx = PosHash & MAX_TT;
  tupd = &(tt[Indx]);
  if (pdepth < (int)tupd->depth) {
    tupd++;
  }
  tupd->flag  = (char)pflag;
  tupd->depth = (char)pdepth;
  tupd->value = pvalue;
  tupd->PositionHashUpper = key32;
  if (hmv.u) {
    tupd->hmove = hmv;
  }
}

/* ----------- SEARCH UTILITY FUNCTIONS ----------------------------- */

void InitTime(void)
{
  start_time = GetMillisecs();
  stop_time = start_time + max_time;
}

int CheckTime(void)
{
  if (GetMillisecs() >= (stop_time-100)) {
    return 1;  
  }
  return 0;
}

int HaveNeighborColummns(int xy1, int xy2)
{
  register int ab = ColNum[xy1] - ColNum[xy2];
  if ( (ab == 1) || (ab == -1) ) {
    return 1;
  } else {
    return 0;
  }
}

int ParsePlayerMove(const char* buf, MOVE *mp, int CheckBadBookMove)
{
  int x1,y1,x2,y2;
  if (strlen(buf)<4)
    return 0;
  if (buf[0]>='a' && buf[0]<='h') {
      x1 = buf[0] - 'a';
      if (buf[1]>='1' && buf[1]<='8') {
        y1 = buf[1] - '1';
        if (buf[2]>='a' && buf[2]<='h') {
          x2 = buf[2] - 'a';
          if (buf[3]>='1' && buf[3]<='8') {
            y2 = buf[3] - '1';
            if (CheckBadBookMove && strlen(buf)>4 && buf[4]=='?') {
              return 0;
            }
          } else {/* not 1-8 */
            return 0;
          }
        } else {/* not a-h */
          return 0;
        }
      }else { /* not 1-8 */
        return 0;
      }
  } else { /* not a-h */
    return 0;
  }
  mp->m.from = 10*y1+x1+21;
  mp->m.to   = 10*y2+x2+21;
  mp->m.mvv_lva=0;
  if (board[mp->m.from]->type==WPAWN) {
    if (mp->m.to>=A8) {
      switch(buf[4]) {
        case 'r': mp->m.flag=WROOK;   break;
        case 'n': mp->m.flag=WKNIGHT; break;
        case 'b': mp->m.flag=WBISHOP; break;
        case 'q': mp->m.flag=WQUEEN;  break;
        default:  break;
      }
    } else mp->m.flag=WPAWN;
  } else if (board[mp->m.from]->type==BPAWN) {
    if (mp->m.to<=H1) {
      switch(buf[4]) {
        case 'r': mp->m.flag=BROOK;   break;
        case 'n': mp->m.flag=BKNIGHT; break;
        case 'b': mp->m.flag=BBISHOP; break;
        case 'q': mp->m.flag=BQUEEN;  break;
        default:  break;
      }
    } else mp->m.flag=BPAWN;
  } else {
    mp->m.flag=1;
  }
  return 1;
}

void PushStatus(void)
{
  cst_p++;
  cstack[cst_p].flags    = gflags;
  cstack[cst_p].EpSquare = EnPassantSq;
}

void PopStatus(void)
{
  gflags = cstack[cst_p].flags;
  EnPassantSq = cstack[cst_p].EpSquare;
  cst_p--;
}

void TryMove(MOVE *mp) /* No ep/castle flags checked */
{
  register int xyc, xydif;
  register int xy1 =mp->m.from;
  register int xy2 =mp->m.to;
  register int flag=mp->m.flag;
  mv_stack_p++;
  move_stack[mv_stack_p].move.u = mp->u;
  move_stack[mv_stack_p].special = NORMAL;
  if (board[xy1]->type==WPAWN) {
    xydif = xy2-xy1;
    if ((xydif==11 || xydif==9) && (board[xy2]->type==0)) { /*En Passant*/
      xyc = xy2-10;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
    } else {
      if (flag>=WKNIGHT && flag<WKING) { /* white pawn promotion. Piece in flag */
        board[xy1]->type = flag;
        move_stack[mv_stack_p].special=PROMOT;
      }
      xyc=xy2;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
    }
  } else if (board[xy1]->type==BPAWN) {
    xydif = xy2-xy1;
    if ((xydif==-11 || xydif==-9) && (board[xy2]->type==0)) { /*En Passant*/
      xyc = xy2+10;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
    } else {
      if (flag>=BKNIGHT && flag<BKING) { /* black pawn promotes to flag */
        board[xy1]->type = flag;
        move_stack[mv_stack_p].special=PROMOT;
      }
      xyc=xy2;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
    }
  } else {
    xyc=xy2;
    move_stack[mv_stack_p].captured = board[xyc];
    move_stack[mv_stack_p].capt = xyc;
  }
  board[xyc]->xy = 0;      /* Captured piece struct modified */
  board[xy1]->xy = xy2;    /* Moving piece struct modified */
  board[xyc] = &empty_p;
  board[xy2] = board[xy1];
  board[xy1] = &empty_p;
  if (board[xy2]->type==WKING) {
    wking = xy2;
    if (xy1==E1) {
       if (xy2==G1) { /* white short castle */
         board[F1] = board[H1];
         board[F1]->xy = F1;
         board[H1] = &empty_p;
         move_stack[mv_stack_p].special = CASTL;
       } else if (xy2==C1) { /* white long castle */
         board[D1] = board[A1];
         board[D1]->xy = D1;
         board[A1] = &empty_p;
         move_stack[mv_stack_p].special = CASTL;
       }
    }
  } else if (board[xy2]->type==BKING) {
     bking = xy2;
     if (xy1==E8) {
       if (xy2==G8) { /* black short castle */
         board[F8] = board[H8];
         board[F8]->xy = F8;
         board[H8] = &empty_p;
         move_stack[mv_stack_p].special = CASTL;
       } else if (xy2==C8) { /* black long castle */
         board[D8] = board[A8];
         board[D8]->xy = D8;
         board[A8] = &empty_p;
         move_stack[mv_stack_p].special = CASTL;
       }
     }
  }
}

void MakeMove(MOVE *mp)
{
  register int xy1, xy2, flag, ptype1, xyc, xydif;
  xy1  = mp->m.from;
  xy2  = mp->m.to;
  flag = mp->m.flag;
  ptype1 = board[xy1]->type;
  mv_stack_p++;
  move_stack[mv_stack_p].move.u = mp->u;
  EnPassantSq=0;
  move_stack[mv_stack_p].special = NORMAL;
  if (ptype1==WPAWN) {
    xydif = xy2-xy1;
    if ((xydif==11 || xydif==9) && (board[xy2]->type==0)) { /*En Passant*/
      xyc = xy2-10;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
    } else {
      if (flag>=WKNIGHT && flag<WKING) { /* white pawn promotion. Piece in flag */
        board[xy1]->type = flag;
        move_stack[mv_stack_p].special=PROMOT;
      }
      xyc=xy2;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
      if (xydif==20) {
        if (board[xy2+1]->type==BPAWN || board[xy2-1]->type==BPAWN) {
          EnPassantSq=xy1+10;
        }
      }
    }
  } else if (ptype1==BPAWN) {
    xydif = xy2-xy1;
    if ((xydif==-11 || xydif==-9) && (board[xy2]->type==0)) { /*En Passant*/
      xyc = xy2+10;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
    } else {
      if (flag>=BKNIGHT && flag<BKING) { /* black pawn promotes to flag */
        board[xy1]->type = flag;
        move_stack[mv_stack_p].special=PROMOT;
      }
      xyc=xy2;
      move_stack[mv_stack_p].captured = board[xyc];
      move_stack[mv_stack_p].capt = xyc;
      if (xydif==-20) {
        if (board[xy2+1]->type==WPAWN || board[xy2-1]->type==WPAWN) {
          EnPassantSq=xy1-10;
        }
      }
    }
  } else {
    xyc=xy2;
    move_stack[mv_stack_p].captured = board[xyc];
    move_stack[mv_stack_p].capt = xyc;
  }
  /* Captured piece struct modified */
  if (board[xyc]->type) {
    board[xyc]->xy = 0;
    board[xyc]->prev->next = board[xyc]->next;
    if (board[xyc]->next) {
      board[xyc]->next->prev = board[xyc]->prev;
    }
    board[xyc] = &empty_p;
  }
  board[xy1]->xy = xy2;    /* Moving piece struct modified */
  board[xy2] = board[xy1];
  board[xy1] = &empty_p;
  /* Update Flags */
  if (board[xy2]->type > black) {
    gflags |= 256; /*black move*/
    if (ptype1==BROOK) {
      if (xy1==A8) {
        gflags |= 16; /*  bra8moved=1;*/
      } else if (xy1==H8) {
        gflags |= 32; /*  brh8moved=1;*/
      }
    } else if (ptype1==BKING) {
      gflags |= 8; /*  bkmoved=1;*/
      bking = xy2;
      if (xy1==E8) {
        if (xy2==G8) { /* black short castle */
          board[F8] = board[H8];
          board[F8]->xy = F8;
          board[H8] = &empty_p;
          move_stack[mv_stack_p].special = CASTL;
          gflags |= 160; /*  BHasCastled=1; and  brh8moved=1;*/
        } else if (xy2==C8) { /* black long castle */
          board[D8] = board[A8];
          board[D8]->xy = D8;
          board[A8] = &empty_p;
          move_stack[mv_stack_p].special = CASTL;
          gflags |= 144; /*  BHasCastled=1; and  bra8moved=1;*/
        }
      }
      if (xy2==G8) {
        if ((board[F8]->type == BROOK) && (board[H8]->xy == 0)) {
          gflags |= 128; /*  artificial BHasCastled=1 */
        }
      }
    }
  } else {
    gflags &= ~256; /*white move*/
    if (ptype1==WROOK) {
      if (xy1==A1) {
        gflags |= 2; /*  wra1moved=1;*/
      } else if (xy1==H1) {
        gflags |= 4; /*  wrh1moved=1;*/
      }
    } else if (ptype1==WKING) {
      wking = xy2;
      if (xy1==E1) {
        gflags |= 1; /* wkmoved=1;*/
        if (xy2==G1) { /* white short castle */
          board[F1] = board[H1];
          board[F1]->xy = F1;
          board[H1] = &empty_p;
          move_stack[mv_stack_p].special = CASTL;
          gflags |= 68; /*  WHasCastled=1; and wrh1moved */
        } else if (xy2==C1) { /* white long castle */
          board[D1] = board[A1];
          board[D1]->xy = D1;
          board[A1] = &empty_p;
          move_stack[mv_stack_p].special = CASTL;
          gflags |= 66; /*  WHasCastled=1; and wra1moved */
        }
      } 
      if (xy2==G1) {
        if ((board[F1]->type == WROOK) && (board[H1]->xy == 0)) {
          gflags |= 64; /*  artificial WHasCastled=1 */
        }
      }
    }
  }
  move_stack[mv_stack_p].PositionHash = GetPositionHash(&move_stack[mv_stack_p].PawnHash);
}

void RetractLastMove(void)
{
  register int xy1=move_stack[mv_stack_p].move.m.from;
  register int xy2=move_stack[mv_stack_p].move.m.to;
  register int cpt=move_stack[mv_stack_p].capt;
  board[xy1] = board[xy2];
  board[xy1]->xy = xy1;
  board[xy2] = &empty_p;
  board[cpt] = move_stack[mv_stack_p].captured;
  if (board[cpt] != &empty_p) {
    board[cpt]->xy = cpt;
    board[cpt]->prev->next = board[cpt];
    if (board[cpt]->next)
      board[cpt]->next->prev = board[cpt];
  }
  if (move_stack[mv_stack_p].special==PROMOT) {
    if (xy1>=A7) { /* white pawn promotion */
      board[xy1]->type  = WPAWN;
    } else  { /* black pawn promotion */
      board[xy1]->type  = BPAWN;
    }
  } else {
    if (board[xy1]->type==WKING) {
      wking=xy1;
    } else if (board[xy1]->type==BKING) {
      bking=xy1;
    }
    if (move_stack[mv_stack_p].special==CASTL) {
     if (xy1==E1) { /* white castle */
       if (xy2==G1) {
         board[H1] = board[F1];
         board[H1]->xy = H1;
         board[F1] = &empty_p;
       } else if (xy2==C1) {
         board[A1] = board[D1];
         board[A1]->xy = A1;
         board[D1] = &empty_p;
       } else ExitErrorMesg("Internal - error in castle moves ");
     } else if (xy1==E8) { /* black castle */
       if (xy2==G8) {
         board[H8] = board[F8];
         board[H8]->xy = H8;
         board[F8] = &empty_p;
       } else if (xy2==C8) {
         board[A8] = board[D8];
         board[A8]->xy = A8;
         board[D8] = &empty_p;
       } else ExitErrorMesg("Internal - error in castle moves ");
     } else ExitErrorMesg("Internal - error in castle moves ");
    }
  }
  mv_stack_p--;
}

/* ---------------- TEXT INPUT/OUTPUT ----------------------- */

char *pieceicon(int x, int y)
{
   static char s[3];
   int c = (x+y)%2 ? ' ' : '-';
   int piece=board[10*y+x+21]->type;
   s[0]=c; s[1]=c; s[2]='\0';
   switch(piece) {
     case WROOK  : s[0] = 'R'; break;
     case WKNIGHT: s[0] = 'N'; break;
     case WBISHOP: s[0] = 'B'; break;
     case WQUEEN : s[0] = 'Q'; break;
     case WKING  : s[0] = 'K'; break;
     case WPAWN  : s[0] = 'o'; break;
     case BROOK  : s[0] = 'r'; break;
     case BKNIGHT: s[0] = 'n'; break;
     case BBISHOP: s[0] = 'b'; break;
     case BQUEEN : s[0] = 'q'; break;
     case BKING  : s[0] = 'k'; break;
     case BPAWN  : s[0] = '@'; break;
   }
   return  s;
}

char ShowPieceIcon(int typ)
{
   switch(typ) {
     case BROOK  :
     case WROOK  : return 'R'; 
     case BKNIGHT: 
     case WKNIGHT: return 'N'; 
     case BBISHOP: 
     case WBISHOP: return 'B'; 
     case BQUEEN : 
     case WQUEEN : return 'Q'; 
     case BKING  : 
     case WKING  : return 'K'; 
     case BPAWN  : 
     case WPAWN  : return 'P'; 
     case 0 : return 'E';
      default: return '?';
   }
}

char * ShowSquare(int xy)
{
  static char sqb[3]={'\0','\0','\0'};
  if (xy==0) {
    sqb[0]=sqb[1]='.';
  } else {
    sqb[0] = (char)((xy%10-1)+'a');
    sqb[1] = (char)((xy/10-2)+'1');
  }
  return sqb;
}

void ShowBoard(void)
{
#ifdef NOBOARD
  fprintf(stderr,"\n<...>\n");
#else
  int x,y, xy, i;
  fprintf(stderr,"\n\n");
  fprintf(stderr,"   +--+--+--+--+--+--+--+--+");
  fprintf(stderr,"\n");
  for (y=7; y>0; y--) {
    fprintf(stderr,"%2d ",y+1);
    for (x=0; x<8; x++) {
      xy=10*y+x+21;
      fprintf(stderr,"|%s",pieceicon(x,y));
    }
    fprintf(stderr,"|   ");
    if (y==7) {
      fprintf(stderr,"\n   +--+--+--+--+--+--+--+--+   ");
      printf("\n");
    } else if (y==6) {
      fprintf(stderr,"\n   +--+--+--+--+--+--+--+--+");
      fprintf(stderr,"\n");
    } else if (y==5) {
      fprintf(stderr,"\n   +--+--+--+--+--+--+--+--+   ");
      printf("\n");
    } else {
      fprintf(stderr,"\n   +--+--+--+--+--+--+--+--+\n");
    }
  }
  fprintf(stderr," 1 ");
  for (x=0; x<8; x++) {
    xy=10*y+x+21;
    fprintf(stderr,"|%s",pieceicon(x,y));
  }
  fprintf(stderr,"|\n   +--+--+--+--+--+--+--+--+\n");
  fprintf(stderr,"    a  b  c  d  e  f  g  h\n\n");
#endif
}

void ReadPosition(char *fname)
{
  FILE *fp;
  char cbuf[81], *cp, mbuf[60];
  int i, color=-1, wkf=0, bkf=0, line=0, Ppos;
  if ((fp=fopen(fname,"r"))==NULL) {
     ExitErrorMesg("Cannot Open position file");
  }
  EmptyBoard();
  while ( fgets(cbuf,80,fp)!=NULL) {
    line++;
    if (strstr(cbuf,"white")!=NULL || strstr(cbuf,"White")!=NULL) {
      color=0;
    } else if (strstr(cbuf,"black")!=NULL || strstr(cbuf,"Black")!=NULL) {
      color=1;
    } else if (color==0) {
      cp = cbuf;
      while (*cp && *(cp+1) && *(cp+2)) {
       switch (*cp) {
        case '\n':
        case '\t':
        case ',':
        case ' ': cp++;
          break;
        case 'K': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8'){
           sprintf(mbuf,"Error in Position line %d ->'K%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          if (wkf==1)
           ExitErrorMesg("Illegal Position. Too many white kings.");
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          wkf=1;
          wking = Ppos;
          board[Ppos] = &Wpieces[0];
          Wpieces[0].xy = Ppos;
          cp+=3;
          break;
        case 'Q': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'Q%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Wpieces[1].xy==0) {
            board[Ppos]=&Wpieces[1];
            Wpieces[1].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Wpieces[i].xy==0) {
                board[Ppos]=&Wpieces[i];
                Wpieces[i].xy = Ppos;
                Wpieces[i].type = WQUEEN;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many white queens.");
              }
            }
          }
          cp+=3;
          break;
        case 'R': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'R%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Wpieces[2].xy==0) {
            board[Ppos]=&Wpieces[2];
            Wpieces[2].xy = Ppos;
          } else if (Wpieces[3].xy==0) {
            board[Ppos]=&Wpieces[3];
            Wpieces[3].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Wpieces[i].xy==0) {
                board[Ppos]=&Wpieces[i];
                Wpieces[i].xy = Ppos;
                Wpieces[i].type = WROOK;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many white rooks.");
              }
            }
          } 
          cp+=3;
          break;
        case 'B': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'B%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Wpieces[4].xy==0) {
            board[Ppos]=&Wpieces[4];
            Wpieces[4].xy = Ppos;
          } else if (Wpieces[5].xy==0) {
            board[Ppos]=&Wpieces[5];
            Wpieces[5].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Wpieces[i].xy==0) {
                board[Ppos]=&Wpieces[i];
                Wpieces[i].xy = Ppos;
                Wpieces[i].type = WBISHOP;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many white bishops.");
              }
            }
          } 
          cp+=3;
          break;
        case 'N': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'N%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Wpieces[6].xy==0) {
            board[Ppos]=&Wpieces[6];
            Wpieces[6].xy = Ppos;
          } else if (Wpieces[7].xy==0) {
            board[Ppos]=&Wpieces[7];
            Wpieces[7].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Wpieces[i].xy==0) {
                board[Ppos]=&Wpieces[i];
                Wpieces[i].xy = Ppos;
                Wpieces[i].type = WKNIGHT;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many white knights.");
              }
            }
          } 
          cp+=3;
          break;
        case 'P': cp++;
        default:
          if (*cp<'a' || *cp>'h' || *(cp+1)<'1' || *(cp+1)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'%c%c'",line,*cp,*(cp+1));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[1]-'1')+cp[0]-'a'+21;
          if (Ppos <= H1 || Ppos >= A8) {
            ExitErrorMesg("Illegal White pawn");
          }
          for (i=8; i<16; i++) {
            if (Wpieces[i].xy==0) {
              board[Ppos]=&Wpieces[i];
              Wpieces[i].xy = Ppos;
              break;
            } else if (i==15) {
              ExitErrorMesg("Illegal Position. Too many white pawns.");
            }
          }
          cp+=2;
          break;
       }
      }
    } else if (color==1) {
      cp = cbuf;
      while (*cp && *(cp+1) && *(cp+2)) {
       switch (*cp) {
        case '\n':
        case '\t':
        case ',':
        case ' ': cp++;
        break;
        case 'K': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'K%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          if (bkf==1)
            ExitErrorMesg("Illegal Position. Too many black kings.");
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          bkf=1;
          bking = Ppos;
          board[Ppos] = &Bpieces[0];
          Bpieces[0].xy = Ppos;
          cp+=3;
          break;
        case 'Q': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'Q%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Bpieces[1].xy==0) {
            board[Ppos]=&Bpieces[1];
            Bpieces[1].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Bpieces[i].xy==0) {
                board[Ppos]=&Bpieces[i];
                Bpieces[i].xy = Ppos;
                Bpieces[i].type = BQUEEN;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many black queens.");
              }
            }
          }
          cp+=3;
          break;
        case 'R': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'R%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Bpieces[2].xy==0) {
            board[Ppos]=&Bpieces[2];
            Bpieces[2].xy = Ppos;
          } else if (Bpieces[3].xy==0) {
            board[Ppos]=&Bpieces[3];
            Bpieces[3].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Bpieces[i].xy==0) {
                board[Ppos]=&Bpieces[i];
                Bpieces[i].xy = Ppos;
                Bpieces[i].type = BROOK;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many black rooks.");
              }
            }
          } 
          cp+=3;
          break;
        case 'B': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'B%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Bpieces[4].xy==0) {
            board[Ppos]=&Bpieces[4];
            Bpieces[4].xy = Ppos;
          } else if (Bpieces[5].xy==0) {
            board[Ppos]=&Bpieces[5];
            Bpieces[5].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Bpieces[i].xy==0) {
                board[Ppos]=&Bpieces[i];
                Bpieces[i].xy = Ppos;
                Bpieces[i].type = BBISHOP;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many black bishops.");
              }
            }
          } 
          cp+=3;
          break;
        case 'N': 
          if (*(cp+1)<'a' || *(cp+1)>'h' || *(cp+2)<'1' || *(cp+2)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'N%c%c'",line,*(cp+1),*(cp+2));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[2]-'1')+cp[1]-'a'+21;
          if (Bpieces[6].xy==0) {
            board[Ppos]=&Bpieces[6];
            Bpieces[6].xy = Ppos;
          } else if (Bpieces[7].xy==0) {
            board[Ppos]=&Bpieces[7];
            Bpieces[7].xy = Ppos;
          } else { /* promoted piece */
            for (i=8; i<16; i++) {
              if (Bpieces[i].xy==0) {
                board[Ppos]=&Bpieces[i];
                Bpieces[i].xy = Ppos;
                Bpieces[i].type = BKNIGHT;
                break;
              } else if (i==15) {
                ExitErrorMesg("Illegal Position. Too many black knights.");
              }
            }
          } 
          cp+=3;
          break;
        case 'P': cp++;
        default:  
          if (*cp<'a' || *cp>'h' || *(cp+1)<'1' || *(cp+1)>'8') {
           sprintf(mbuf,"Error in Position line %d ->'%c%c'",line,*cp,*(cp+1));
           ExitErrorMesg(mbuf);
          }
          Ppos = 10*(cp[1]-'1')+cp[0]-'a'+21;
          if (Ppos <= H1 || Ppos >= A8) {
            ExitErrorMesg("Illegal Black pawn");
          }
          for (i=8; i<16; i++) {
            if (Bpieces[i].xy==0) {
              board[Ppos]=&Bpieces[i];
              Bpieces[i].xy = Ppos;
              break;
            } else if (i==15) {
              ExitErrorMesg("Illegal Position. Too many black pawns.");
            }
          }
          cp+=2;
          break;
       }
      }
    }

  }
  fclose(fp);
  if (!wkf || !bkf) {
    ExitErrorMesg("Illegal Position. King(s) missing");
  }
  /* Fix non board piece pointers */
  for (PIECE *p=Bpieces[0].next; p!=NULL; p=p->next) {
    if (p->xy == 0) {
      p->prev->next = p->next;
      if (p->next)
        p->next->prev = p->prev;
    }
  }
  for (PIECE *p=Wpieces[0].next; p!=NULL; p=p->next) {
    if (p->xy == 0) {
      p->prev->next = p->next;
      if (p->next)
        p->next->prev = p->prev;
    }
  }
  /* castling flags reset*/  
  if (wking==E1) { 
    gflags &= (~1); /* wkmoved=0;*/
    gflags &= (~64); /* WHasCastled=0; */
  } else { 
    gflags |= 1;  /*  wkmoved=1; */
    gflags  |= 64; /*  WHasCastled=1;*/
  }
  if (bking==E8) { 
    gflags &= (~8); /*  bkmoved=0; */
    gflags &= (~128); /*  BHasCastled=0;*/
  } else { 
    gflags |= 8; /*   bkmoved=1; */
    gflags |= 128; /*  BHasCastled=1;*/
  }
  if (board[A1]->type==WROOK) { gflags &= (~2); /*wra1moved=0;*/ } else { gflags |= 2; /*wra1moved=1;*/ }
  if (board[H1]->type==WROOK) { gflags &= (~4); /*wrh1moved=0; */} else { gflags |= 4; /*wrh1moved=1;*/ }
  if (board[A8]->type==BROOK) { gflags &= (~16); /*bra8moved=0;*/} else { gflags |= 16; /*bra8moved=1;*/}
  if (board[H8]->type==BROOK) { gflags &= (~32); /*brh8moved=0;*/} else { gflags |= 32; /*brh8moved=1;*/}
  EnPassantSq=0;
  /* Move Stack Pointers reset */
  cst_p=0;
  mv_stack_p=0;
  HalfMovesPlayed=0;
  CurrentLine[0] = '\0';
  LoneKingReachedEdge=0;
  FiftyMoves=0;
  NotStartingPosition=1;
  PlayerMove.u=0;
}

/* --------------- MOVE GENERATION ---------------------------------- */

int WhiteKingInCheckInfo(MOVE AttackSq[], int *Attackers)
{
  register int xyk=wking, xy, i, test, nextfree=0;
  MOVE mp;
  int nLine=0, Linexy[MAXMV];
  mp.m.to      = xyk;
  mp.m.mvv_lva = 0;
  *Attackers   = 0;
  /* black pawn checks and some knights square */
  xy=xyk+8;
  if (board[xy]->type==BKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy++;
  if (board[xy]->type==BPAWN) { /* += 9*/
    mp.m.from    = xy;
    mp.m.flag    = BPAWN;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy++;
  xy++;
  if (board[xy]->type==BPAWN) { /* += 11 */
    mp.m.from    = xy;
    mp.m.flag    = BPAWN;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy++;
  if (board[xy]->type==BKNIGHT) { /* += 12*/
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk-12;
  if (board[xy]->type==BKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk-8;
  if (board[xy]->type==BKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  /* remaining black knight checks */
  xy=xyk+21;
  if (board[xy]->type==BKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk-21;
  if (board[xy]->type==BKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk+19;
  if (board[xy]->type==BKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk-19;  
  if (board[xy]->type==BKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = BKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  /* black bishop or queen checks */
  xy=xyk;
  for (;;) {
    xy+=9;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy-=9;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy+=11;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy-=11;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  /* black rook or queen checks */
  nLine=0;
  xy=xyk;
  for (;;) {
    xy++;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else {
      if(test==BROOK || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy--;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else {
      if(test==BROOK || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy+=10;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else  {
      if(test==BROOK || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy-=10;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        Linexy[nLine] = xy;
        nLine++;
        continue;
      }
      break;
    } else {
      if(test==BROOK || test==BQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  return nextfree;
}

int WhiteKingInCheck(void)
{
  register int xyk=wking, xy;
  register int test;
  /* black pawn checks & kings side by side and some knights square */
  xy=xyk+8;
  if (board[xy]->type==BKNIGHT)
    return 1;
  xy++;
  test = board[xy]->type;
  if (test==BPAWN || test==BKING) /* += 9*/
    return 1;
  xy++;
  if (board[xy]->type==BKING)  /* += 10*/
    return 1;
  xy++;
  test = board[xy]->type;
  if (test==BPAWN || test==BKING)  /* += 11 */
    return 1;
  xy++;
  if (board[xy]->type==BKNIGHT)  /* += 12*/
    return 1;
  xy=xyk-12;
  if (board[xy]->type==BKNIGHT)
    return 1;
  xy++;
  if (board[xy]->type==BKING) /* -=11; */
    return 1;
  xy++;
  if (board[xy]->type==BKING)  /* -=10 */
    return 1;
  xy++;
  if (board[xy]->type==BKING)  /* -=9 */
    return 1;
  xy++;
  if (board[xy]->type==BKNIGHT)  /* -=8 */
    return 1;
  if (board[xyk-1]->type==BKING)
    return 1;
  if (board[xyk+1]->type==BKING)
    return 1;
  /* remaining black knight checks */
  if (board[xyk+21]->type==BKNIGHT || board[xyk-21]->type==BKNIGHT)
    return 1;
  if (board[xyk+19]->type==BKNIGHT || board[xyk-19]->type==BKNIGHT)
    return 1;
  /* black bishop or queen checks */
  xy=xyk;
  for (;;) {
    xy+=9;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  xy=xyk;
  for (;;) {
    xy-=9;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  xy=xyk;
  for (;;) {
    xy+=11;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  xy=xyk;
  for (;;) {
    xy-=11;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else {
      if(test==BBISHOP || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  /* black rook or queen checks */
  xy=xyk;
  for (;;) {
    xy++;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else {
      if(test==BROOK || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  xy=xyk;
  for (;;) {
    xy--;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else {
      if(test==BROOK || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  xy=xyk;
  for (;;) {
    xy+=10;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else  {
      if(test==BROOK || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  xy=xyk;
  for (;;) {
    xy-=10;
    test = board[xy]->type;
    if (test<black) {
      if (test==0) {
        continue;
      }
      break;
    } else {
      if(test==BROOK || test==BQUEEN) {
        return 1;
      }
      break;
    }
  }
  return 0;
}

void AddWhiteMv(int xy0, int xy, int flag, MOVE q[], int *nextf, int MvvLva, int level=-1)
{
  MOVE mp;
  register int W_history_hit=0;
  mp.m.from    = xy0;
  mp.m.to      = xy;
  mp.m.flag    = flag;
  if (MvvLva==0) {
    if (level>=0) {
      if ( W_Killers[0][level] == mp.u ) {
        mp.m.mvv_lva = 1;
      } else if ( W_Killers[1][level] == mp.u ) {
        mp.m.mvv_lva = 0;
      } else {
        W_history_hit = W_history[ board[xy0]->type - WPAWN ][xy];
      } 
    } else {
      W_history_hit = W_history[ board[xy0]->type - WPAWN ][xy];
    }
    if (W_history_hit != 0) {
      mp.m.mvv_lva = W_history_hit;
    } else {
      if (xy>bking) {
        mp.m.mvv_lva = bking-xy-MAX_DEPTH;
      } else {
        mp.m.mvv_lva = xy-bking-MAX_DEPTH;
      }
    }
  } else {
    mp.m.mvv_lva = MvvLva;
  }
  q[*nextf].u = mp.u;
  (*nextf) ++;
}

int SquareExistsInAttack(int xy, MOVE qAttacks[], int nA)
{
  register int j;
  for (j=0; j<nA; j++) {
    if (qAttacks[j].m.from == xy)
      return 1;
  }
  return 0;
}

void AddWhiteBishopCaptures(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece)
{
  register int xy=xy0, bmoves=0, test;
  for (;;) {
     xy+=9;
     test = board[xy]->type;
     if (test==0) {
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=9;
     test = board[xy]->type;
     if (test==0) {
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy+=11;
     test = board[xy]->type;
     if (test==0) {
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=11;
     test = board[xy]->type;
     if (test==0) {
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  (*mobilityP) += bmoves;
}

void AddWhiteBishopMoves(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, int level=-1)
{
  register int xy=xy0, bmoves=0, test;
  for (;;) {
     xy+=9;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=9;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy+=11;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=11;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       bmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       bmoves++;
       break;
     } else {
       break;
     }
  }
  (*mobilityP) += bmoves;
}

void AddWhiteBishopEvasions(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, MOVE qAttacks[], int nA)
{
  register int xy=xy0, bmoves=0, test;
  for (;;) {
     xy+=9;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       bmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=9;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       bmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy+=11;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       bmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       bmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=11;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       bmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       bmoves++;
       break;
     } else {
       break;
     }
  }
  (*mobilityP) += bmoves;
}

void AddWhiteKnightCaptures(int xy0, MOVE q[], int *nextf, int *mobilityP)
{
  register int xy, nmoves=0, test;
  xy = xy0 + 21;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 21;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 + 19;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 19;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 + 12;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 12;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 + 8;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 8;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  (*mobilityP) += nmoves;
}

void AddWhiteKnightMoves(int xy0, MOVE q[], int *nextf, int *mobilityP, int level=-1)
{
  register int xy, nmoves=0, test;
  xy = xy0 + 21;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT ,level);
    nmoves++;
  }
  xy = xy0 - 21;
  test = board[xy]->type;
  if (test==0){
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT ,level);
    nmoves++;
  }
  xy = xy0 + 19;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT ,level);
    nmoves++;
  }
  xy = xy0 - 19;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT ,level);
    nmoves++;
  }
  xy = xy0 + 12;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT ,level);
    nmoves++;
  }
  xy = xy0 - 12;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT ,level);
    nmoves++;
  }
  xy = xy0 + 8;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT ,level);
    nmoves++;
  }
  xy = xy0 - 8;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    nmoves++;
  }
  (*mobilityP) += nmoves;
}

void AddWhiteKnightEvasions(int xy0, MOVE q[], int *nextf, int *mobilityP, MOVE qAttacks[], int nA)
{

  register int xy, nmoves=0, test;
  xy = xy0 + 21;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  xy = xy0 - 21;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  xy = xy0 + 19;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  xy = xy0 - 19;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  xy = xy0 + 12;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  xy = xy0 - 12;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  xy = xy0 + 8;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  xy = xy0 - 8;
  test = board[xy]->type;
  if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  } else if (test>black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-WKNIGHT );
    }
    nmoves++;
  }
  (*mobilityP) += nmoves;
}                        

void AddWhiteRookCaptures(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece)
{
  register int xy=xy0, rmoves=0, test;
  for (;;) {
     xy++;
     test = board[xy]->type;
     if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else if (test==0) {
       rmoves++;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy--;
     test = board[xy]->type;
     if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else if (test==0) {
       rmoves++;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy+=10;
     test = board[xy]->type;
     if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else if (test==0) {
       rmoves++;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=10;
     test = board[xy]->type;
     if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else if (test==0) {
       rmoves++;
     } else {
       break;
     }
  }
  (*mobilityP) += rmoves;
}

void AddWhiteRookMoves(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, int level=-1)
{
  register int xy=xy0, rmoves=0, test;
  for (;;) {
     xy++;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       rmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       rmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy--;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       rmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       rmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy+=10;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       rmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       rmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=10;
     test = board[xy]->type;
     if (test==0) {
       AddWhiteMv(xy0,xy,1,q,nextf,0,level);
       rmoves++;
     } else if (test>black) {
       AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece ,level);
       rmoves++;
       break;
     } else {
       break;
     }
  }
  (*mobilityP) += rmoves;
}

void AddWhiteRookEvasions(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, MOVE qAttacks[], int nA)
{
  register int xy=xy0, rmoves=0, test;
  for (;;) {
     xy++;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       rmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy--;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       rmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy+=10;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       rmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else {
       break;
     }
  }
  xy=xy0;
  for (;;) {
     xy-=10;
     test = board[xy]->type;
     if (test==0) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf,0);
       rmoves++;
     } else if (test>black) {
      if (SquareExistsInAttack(xy, qAttacks, nA))
         AddWhiteMv(xy0,xy,1,q,nextf, ((test-black) << 4)-piece );
       rmoves++;
       break;
     } else {
       break;
     }
  }
  (*mobilityP) += rmoves;
}

void AddWhitePawnNoCapsNoPromMoves(int xy0, MOVE q[], int *nextf, int level=-1)
{
  register int xy=xy0;
  xy += 10;
  if (board[xy]->type==0) {
    if (xy0<A7) { /*not in 7th rank */
      AddWhiteMv(xy0,xy,WPAWN,q,nextf,(xy>=A6) ,level);
    }
    if (xy0<=H2) { /* Two step pawn move*/
      xy += 10;
      if (board[xy]->type==0) {
        AddWhiteMv(xy0,xy,WPAWN,q,nextf,0,level);
      }
    }
  }
}

void AddWhitePawnCapturesAndPromotions(int xy0, MOVE q[], int *nextf)
{
  /* !! Attention. If promotion the promotion piece is saved in q[i]->flag*/
  register int xy, test;
  if (xy0>=A7) {  /* promotion */
    xy = xy0+9;
    test = board[xy]->type;
    if (test>black) {
      AddWhiteMv(xy0,xy,WQUEEN,q,nextf, ((test-14+WQUEEN) << 4)-WPAWN /*mvv lva*/);
      AddWhiteMv(xy0,xy,WKNIGHT,q,nextf, ((test-14+WKNIGHT) << 4)-WPAWN);
      AddWhiteMv(xy0,xy,WROOK,q,nextf, ((test-14+WROOK) << 4)-WPAWN);
      AddWhiteMv(xy0,xy,WBISHOP,q,nextf, ((test-14+WBISHOP) << 4)-WPAWN);
    }
    xy++; /* = xy0+10;*/
    test = board[xy]->type;
    if (test==0) {
      AddWhiteMv(xy0,xy,WQUEEN,q,nextf, (WQUEEN << 4)-WPAWN /*mvv lva*/);
      AddWhiteMv(xy0,xy,WKNIGHT,q,nextf, (WKNIGHT << 4)-WPAWN);
      AddWhiteMv(xy0,xy,WROOK,q,nextf, (WROOK << 4)-WPAWN);
      AddWhiteMv(xy0,xy,WBISHOP,q,nextf, (WBISHOP << 4)-WPAWN);
    }
    xy++; /* = xy0+11;*/
    test = board[xy]->type;
    if (test>black) {
      AddWhiteMv(xy0,xy,WQUEEN,q,nextf, ((test-14+WQUEEN) << 4)-WPAWN /*mvv lva*/);
      AddWhiteMv(xy0,xy,WKNIGHT,q,nextf, ((test-14+WKNIGHT) << 4)-WPAWN);
      AddWhiteMv(xy0,xy,WROOK,q,nextf, ((test-14+WROOK) << 4)-WPAWN);
      AddWhiteMv(xy0,xy,WBISHOP,q,nextf, ((test-14+WBISHOP) << 4)-WPAWN);
    }
  } else {
    xy=xy0+9;
    test = board[xy]->type;
    if (test>black) {
      AddWhiteMv(xy0,xy,WPAWN,q,nextf, ((test-black) << 4)-WPAWN /*mvv lva*/);
    } else if (xy==EnPassantSq) {
      AddWhiteMv(xy0,xy,WPAWN,q,nextf, (WPAWN << 4)-WPAWN);  /* en passant */
    }

    xy=xy0+11;
    test = board[xy]->type;
    if (test>black) {
      AddWhiteMv(xy0,xy,WPAWN,q,nextf, ((test-black) << 4)-WPAWN /*mvv lva*/);
    } else if (xy==EnPassantSq) {
      AddWhiteMv(xy0,xy,WPAWN,q,nextf, (WPAWN << 4)-WPAWN);  /* en passant */
    }
  }
}

void AddWhiteKingMoves(int xy0, MOVE q[], int *nextf)
{
  register int xy, test;
  xy = xy0 + 1;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 - 1;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 + 9;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 + 10;*/
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 + 11;*/
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 - 11;
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 - 10;*/
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 - 9;*/
  test = board[xy]->type;
  if (test==0) {
    AddWhiteMv(xy0,xy,1,q,nextf,0);
  } else if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }

  if ( (gflags&1)==0 /*!wkmoved*/ && xy0==E1) {
    if ( (gflags&4)==0 /*!wrh1moved*/ && board[H1]->type==WROOK) {
      if (!WhiteKingInCheck() && board[F1]->type==0 && board[G1]->type==0) {
        wking=F1;
        if (!WhiteKingInCheck()) {
          AddWhiteMv(E1,G1,1,q,nextf,100);
        }
        wking=E1;
      }
    }
    if ( (gflags&2)==0 /*!wra1moved*/ && board[A1]->type==WROOK) {
      if (!WhiteKingInCheck()) {
        if (board[D1]->type==0 && board[C1]->type==0 && board[B1]->type==0) {
          wking=D1;
          if (!WhiteKingInCheck()) {
            AddWhiteMv(E1,C1,1,q,nextf,90);
          }
          wking=E1;
        }
      }
    }
  }
}

void AddWhiteKingCaptures(int xy0, MOVE q[], int *nextf)
{
  register int xy, test;
  xy = xy0 + 1;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 - 1;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 + 9;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 + 10;*/
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 + 11;*/
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 - 11;
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 - 10;*/
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 - 9;*/
  test = board[xy]->type;
  if (test>black) {
    AddWhiteMv(xy0,xy,1,q,nextf,((test-black) << 4)-WKING /*mvv lva*/);
  }
}

int MOVE_cmp_by_mvv_lva(const void *a, const void *b) 
{ 
    MOVE *ia = (MOVE *)a;
    MOVE *ib = (MOVE *)b;
    return (int)ib->m.mvv_lva - (int)ia->m.mvv_lva;
} 

int FindAllWhiteEvasions(MOVE q[], MOVE qAttacks[], int nA, int nAPieces)
{
  register int test, j;
  int nextfree=0;
  AddWhiteKingMoves(Wpieces[0].xy,q,&nextfree);
  if (nAPieces>1) { /* If double check we are done */
    return nextfree;
  }
  for (PIECE *p=Wpieces[0].next; p!=NULL; p=p->next) {
    p->mobility = 0;
    switch (p->type) { 
      case WPAWN  : for (j=0; j<nA; j++) {
                      test = Abs(boardXY[qAttacks[j].m.from] - boardXY[p->xy]);
                      if (test==9 || test==7 || test==8 || test==16 || test==1) {
                        AddWhitePawnCapturesAndPromotions(p->xy,q,&nextfree);
                        AddWhitePawnNoCapsNoPromMoves(p->xy,q,&nextfree);
                        break;
                      }
                    }
                    break;
      case WKNIGHT: for (j=0; j<nA; j++) {
                      test = Abs(boardXY[qAttacks[j].m.from] - boardXY[p->xy]);
                      if (test==10 || test==17 || test==15 || test==6) {
                        AddWhiteKnightEvasions(p->xy, q, &nextfree, &(p->mobility), qAttacks, nA);
                        p->mobility -= 4;
                        break;
                      }
                    }
                    break;
      case WBISHOP: for (j=0; j<nA; j++) {
                      test = (boardXY[qAttacks[j].m.from] - boardXY[p->xy]);
                      if (test%9==0 || test%7==0) {
                        AddWhiteBishopEvasions(p->xy,q,&nextfree,&(p->mobility),WBISHOP, qAttacks, nA);
                        p->mobility -= 6;
                        break;
                      }
                    }
                    break;
      case WROOK  : AddWhiteRookEvasions(p->xy,q,&nextfree,&(p->mobility),WROOK, qAttacks, nA);
                    p->mobility -= 7;
                    break;
      case WQUEEN : AddWhiteRookEvasions(p->xy,q,&nextfree,&(p->mobility),WQUEEN, qAttacks, nA);
                    AddWhiteBishopEvasions(p->xy,q,&nextfree,&(p->mobility),WQUEEN, qAttacks, nA);
                    p->mobility -= 13;
                    break;
    }
  }
  return nextfree;
}

int FindAllWhiteMoves(MOVE q[], int level=-1)
{
  int nextfree=0;
  /* Find Moves plus mobility value for Rooks,Queens,Bishops,Knights. */
  /* Also subtract mobility normalization value */
  for (PIECE *p=Wpieces[0].next; p!=NULL; p=p->next) {
    p->mobility = 0;
    switch (p->type) { 
      case WPAWN  : AddWhitePawnCapturesAndPromotions(p->xy,q,&nextfree);
                    AddWhitePawnNoCapsNoPromMoves(p->xy,q,&nextfree,level);
                    break;
      case WKNIGHT: AddWhiteKnightMoves(p->xy,q,&nextfree,&(p->mobility),level);
                    p->mobility -= 4;
                    break;
      case WBISHOP: AddWhiteBishopMoves(p->xy,q,&nextfree,&(p->mobility),WBISHOP,level);
                    p->mobility -= 6;
                    break;
      case WROOK  : AddWhiteRookMoves(p->xy,q,&nextfree,&(p->mobility),WROOK,level);
                    p->mobility -= 7;
                    break;
      case WQUEEN : AddWhiteRookMoves(p->xy,q,&nextfree,&(p->mobility),WQUEEN,level);
                    AddWhiteBishopMoves(p->xy,q,&nextfree,&(p->mobility),WQUEEN,level);
                    p->mobility -= 13;
                    break;
    }
  }
  AddWhiteKingMoves(Wpieces[0].xy,q,&nextfree);
  /* Movement sorting is not done here but later in search, so we can use improved info */
  return nextfree;
}

int FindAllWhiteCapturesAndPromotions(MOVE q[]) /* This is used in quiescence search */
{
  int nextfree=0;
  /* Find Moves plus mobility value for Rooks,Queens,Bishops,Knights. */
  /* Also subtract mobility normalization value */
  for (PIECE *p=Wpieces[0].next; p!=NULL; p=p->next) {
    p->mobility = 0;
    switch (p->type) { 
      case WPAWN  : AddWhitePawnCapturesAndPromotions(p->xy,q,&nextfree);
                    break;
      case WKNIGHT: AddWhiteKnightCaptures(p->xy,q,&nextfree,&(p->mobility));
                    p->mobility -= 4;
                    break;
      case WBISHOP: AddWhiteBishopCaptures(p->xy,q,&nextfree,&(p->mobility),WBISHOP);
                    p->mobility -= 6;
                    break;
      case WROOK  : AddWhiteRookCaptures(p->xy,q,&nextfree,&(p->mobility),WROOK);
                    p->mobility -= 7;
                    break;
      case WQUEEN : AddWhiteRookCaptures(p->xy,q,&nextfree,&(p->mobility),WQUEEN);
                    AddWhiteBishopCaptures(p->xy,q,&nextfree,&(p->mobility),WQUEEN);
                    p->mobility -= 13;
                    break;
    }
  }
  AddWhiteKingCaptures(Wpieces[0].xy,q,&nextfree);
  /* Initial Sort of Moves using MVV/LVA (Most Valuable Victim/Least Valuable Attacker) for captures. */
  qsort(q, nextfree, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
  return nextfree;
}

void AddMoveToLine(int from, int to)
{
  static char LineMov[10]={"xxxx "};
  int fromx,fromy,tox,toy;
  HalfMovesPlayed++;
  if (HalfMovesPlayed > 40)
    return;
  fromx = from%10 - 1;
  tox   = to%10 - 1;
  fromy = from/10 - 2;
  toy   = to/10 - 2;
  LineMov[0] = (char)fromx + 'a';
  LineMov[1] = (char)fromy + '1';
  LineMov[2] = (char)tox + 'a';
  LineMov[3] = (char)toy + '1';
  strcat(CurrentLine, LineMov);
}

char *TranslateMoves(MOVE *m)
{
  static char mov[10]={"<HT>  "};
  if (m->u) {
    char fromx,fromy,tox,toy;
    fromx = m->m.from%10 - 1;
    tox   = m->m.to%10 - 1;
    fromy = m->m.from/10 - 2;
    toy   = m->m.to/10 - 2;
    mov[0] = fromx + 'a';
    mov[1] = fromy + '1';
    mov[2] = tox + 'a';
    mov[3] = toy + '1';
    mov[4] = '\0';
    mov[5] = '\0';
    switch(m->m.flag) {
      case WROOK  : 
      case BROOK  : 
        mov[4] = 'r'; break;
      case WKNIGHT: 
      case BKNIGHT: 
        mov[4] = 'n'; break;
      case WBISHOP: 
      case BBISHOP: 
        mov[4] = 'b'; break;
      case WQUEEN : 
      case BQUEEN : 
        mov[4] = 'q'; break;
    }
  }
  return mov;
}

void PrintfPVline(LINE *aPVp, int Goodmove)
{
  int i;
  for (i=0; i<aPVp->cmove; i++) {
    if (i==0 && Goodmove) {
      printf("%s! ", TranslateMoves(&(aPVp->argmove[i])));
    } else {
      printf("%s ", TranslateMoves(&(aPVp->argmove[i])));
    }
  }
  printf("\n");
}

int BlackKingInCheckInfo(MOVE AttackSq[], int *Attackers)
{
  register int xyk=bking, xy, i, test, nextfree=0;
  MOVE mp;
  int nLine=0, Linexy[MAXMV];
  mp.m.to      = xyk;
  mp.m.mvv_lva = 0;
  *Attackers   = 0;
  /* white pawn and knight checks */
  xy=xyk-12;
  if (board[xy]->type==WKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy++;
  if (board[xy]->type==WPAWN) { /* -= 11*/
    mp.m.from    = xy;
    mp.m.flag    = WPAWN;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy++;
  xy++;
  if (board[xy]->type==WPAWN) { /* -= 9*/
    mp.m.from    = xy;
    mp.m.flag    = WPAWN;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy++;
  if (board[xy]->type==WKNIGHT) { /* -= 8*/
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk+8;
  if (board[xy]->type==WKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk+12;
  if (board[xy]->type==WKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk+21;
  if (board[xy]->type==WKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk-21;
  if (board[xy]->type==WKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk+19;
  if (board[xy]->type==WKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  xy=xyk-19;
  if (board[xy]->type==WKNIGHT) {
    mp.m.from    = xy;
    mp.m.flag    = WKNIGHT;
    AttackSq[nextfree].u = mp.u;
    nextfree++;
    (*Attackers)++;
  }
  /* white bishop or queen checks */
  xy=xyk;
  for (;;) {
    xy += 9;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy -= 9;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy += 11;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy -= 11;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  /* white rook or queen checks */
  nLine=0;
  xy=xyk;
  for (;;) {
    xy++;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy--;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy += 10;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  nLine=0;
  xy=xyk;
  for (;;) {
    xy -= 10;
    test=board[xy]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      Linexy[nLine] = xy;
      nLine++;
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        for (i=0; i<nLine; i++) {
          mp.m.from    = Linexy[i];
          mp.m.flag    = test;
          AttackSq[nextfree].u = mp.u;
          nextfree++;
        }
        mp.m.from    = xy;
        mp.m.flag    = test;
        AttackSq[nextfree].u = mp.u;
        nextfree++;
        (*Attackers)++;
        if ((*Attackers) > 1) {
          return nextfree;
        }
      }
      break;
    }
  }
  return nextfree;
}

int BlackKingInCheck(void)
{
  register int xy=bking, xyk;
  register int test;
  /* white pawn checks &  kings side by side & some knight squares*/
  xyk = xy-12;
  if (board[xyk]->type==WKNIGHT)
    return 1;
  xyk++; 
  test=board[xyk]->type;
  if (test==WPAWN || test==WKING) /* = xy-11; */
    return 1;
  xyk++;
  if (board[xyk]->type==WKING)    /* = xy-10; */
    return 1;
  xyk++;
  test=board[xyk]->type;
  if (test==WPAWN || test==WKING)  /* = xy-9; */
    return 1;
  xyk++;
  if (board[xyk]->type==WKNIGHT)    /* = xy-8; */
    return 1;
  xyk=xy+8;
  if (board[xyk]->type==WKNIGHT)
    return 1;
  xyk++;
  if (board[xyk]->type==WKING) /*=xy+9;*/
    return 1;
  xyk++;
  if (board[xyk]->type==WKING) /*=xy+10;*/
    return 1;
  xyk++;
  if (board[xyk]->type==WKING) /*=xy+11;*/
    return 1;
  xyk++;
  if (board[xyk]->type==WKNIGHT) /*=xy+12;*/
    return 1;
  if (board[xy-1]->type==WKING)
    return 1;
  if (board[xy+1]->type==WKING)
    return 1;
  /* white knight checks */
  if (board[xy+21]->type==WKNIGHT || board[xy-21]->type==WKNIGHT)
    return 1;
  if (board[xy+19]->type==WKNIGHT || board[xy-19]->type==WKNIGHT)
    return 1;
  /* white bishop or queen checks */
  xyk=xy;
  for (;;) {
    xyk += 9;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  xyk=xy;
  for (;;) {
    xyk -= 9;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  xyk=xy;
  for (;;) {
    xyk += 11;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  xyk=xy;
  for (;;) {
    xyk -= 11;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WBISHOP || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  /* white rook or queen checks */
  xyk=xy;
  for (;;) {
    xyk++;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  xyk=xy;
  for (;;) {
    xyk--;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  xyk=xy;
  for (;;) {
    xyk += 10;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  xyk=xy;
  for (;;) {
    xyk -= 10;
    test=board[xyk]->type;
    if (test>black) {
      break;
    } else if (test==0) {
      continue;
    } else {
      if (test==WROOK || test==WQUEEN) {
        return 1;
      }
      break;
    }
  }
  return 0;
}

void AddBlackMv(int xy0, int xy, int flag, MOVE q[], int *nextf, int MvvLva, int level=-1)
{
  MOVE mp;
  register int B_history_hit=0;
  mp.m.from    = xy0;
  mp.m.to      = xy;
  mp.m.flag    = flag;
  if (MvvLva==0) {
    if (level>=0) {
      if ( B_Killers[0][level] == mp.u ) {
        mp.m.mvv_lva = 1;
      } else if ( B_Killers[1][level] == mp.u ) {
        mp.m.mvv_lva = 0;
      } else {
        B_history_hit = B_history[ board[xy0]->type - BPAWN ][xy];
      } 
    } else {
      B_history_hit = B_history[ board[xy0]->type - BPAWN ][xy];
    }
    if (B_history_hit != 0) {
      mp.m.mvv_lva = B_history_hit;
    } else {
      if (xy>wking) {
        mp.m.mvv_lva = wking-xy-MAX_DEPTH;
      } else {
        mp.m.mvv_lva = xy-wking-MAX_DEPTH;
      }
    }
  } else {
    mp.m.mvv_lva = MvvLva;
  }
  q[*nextf].u = mp.u;
  (*nextf)++;
}

void AddBlackBishopCaptures(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece)
{
  register int xy=xy0, bmoves=0, test;
  for (;;) {
    xy+=11;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=11;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy+=9;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=9;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  (*mobilityP) += bmoves;
}

void AddBlackBishopMoves(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, int level=-1)
{
  register int xy=xy0, bmoves=0, test;
  for (;;) {
    xy+=11;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=11;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy+=9;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=9;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  (*mobilityP) += bmoves;
}

void AddBlackBishopEvasions(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, MOVE qAttacks[], int nA)
{
  register int xy=xy0, bmoves=0, test;
  for (;;) {
    xy+=11;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=11;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy+=9;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=9;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      bmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA))
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  (*mobilityP) += bmoves;
}

void AddBlackKnightCaptures(int xy0, MOVE q[], int *nextf, int *mobilityP)
{
  register int xy, nmoves=0, test;
  xy = xy0 + 21;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 21;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 + 19;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 19;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 + 12;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 12;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 + 8;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  xy = xy0 - 8;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    nmoves++;
  } else if (test==0) {
    nmoves++;
  }
  (*mobilityP) += nmoves;
}

void AddBlackKnightMoves(int xy0, MOVE q[], int *nextf, int *mobilityP, int level=-1)
{
  register int xy, nmoves=0, test;
  xy = xy0 + 21;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  xy = xy0 - 21;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  xy = xy0 + 19;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  xy = xy0 - 19;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  xy = xy0 + 12;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  xy = xy0 - 12;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  xy = xy0 + 8;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  xy = xy0 - 8;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT ,level);
    nmoves++;
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0,level);
    nmoves++;
  }
  (*mobilityP) += nmoves;
}

void AddBlackKnightEvasions(int xy0, MOVE q[], int *nextf, int *mobilityP, MOVE qAttacks[], int nA)
{
  register int xy, nmoves=0, test;
  xy = xy0 + 21;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  xy = xy0 - 21;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  xy = xy0 + 19;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  xy = xy0 - 19;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  xy = xy0 + 12;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  xy = xy0 - 12;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  xy = xy0 + 8;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  xy = xy0 - 8;
  test = board[xy]->type;
  if (test>0 && test<black) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-WKNIGHT );
    }
    nmoves++;
  } else if (test==0) {
    if (SquareExistsInAttack(xy, qAttacks, nA)) {
      AddBlackMv(xy0,xy,1,q,nextf,0);
    }
    nmoves++;
  }
  (*mobilityP) += nmoves;
}

void AddBlackRookCaptures(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece)
{
  register int xy=xy0, rmoves=0, test;
  for (;;) {
    xy--;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy++;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=10;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy+=10;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      }
    }
  }
  (*mobilityP) += rmoves;
}

void AddBlackRookMoves(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, int level=-1)
{
  register int xy=xy0, rmoves=0, test;
  for (;;) {
    xy--;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy++;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=10;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy+=10;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece ,level);
        break;
      } else {
        AddBlackMv(xy0,xy,1,q,nextf,0,level); 
      }
    }
  }
  (*mobilityP) += rmoves;
}

void AddBlackRookEvasions(int xy0, MOVE q[], int *nextf, int *mobilityP, int piece, MOVE qAttacks[], int nA)
{
  register int xy=xy0, rmoves=0, test;
  for (;;) {
    xy--;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy++;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy-=10;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  xy=xy0;
  for (;;) {
    xy+=10;
    test = board[xy]->type;
    if (test>black || test<0) {
      break;
    } else {
      rmoves++;      
      if (test!=0) {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf, (test << 4)-piece );
        break;
      } else {
        if (SquareExistsInAttack(xy, qAttacks, nA)) 
          AddBlackMv(xy0,xy,1,q,nextf,0); 
      }
    }
  }
  (*mobilityP) += rmoves;
}

void AddBlackPawnNonCapsNoProm(int xy0, MOVE q[], int *nextf, int level=-1)
{
  register int xy=xy0;
  xy-=10;
  if (board[xy]->type==0) {
    if (xy0>H2) { /* not in 2nd rank */
      AddBlackMv(xy0,xy,BPAWN,q,nextf,(xy<=H3),level);
    }
    if (xy0>=A7) { /*two step pawn move*/
      xy -= 10;
      if (board[xy]->type==0) {
        AddBlackMv(xy0,xy,BPAWN,q,nextf,0,level);
      }
    }
  }
}

void AddBlackPawnCapturesAndPromotions(int xy0, MOVE q[], int *nextf)
{
  /* !! Attention. If promotion the promotion piece is saved in q[i].flag */
  register int xy=xy0, test;
  if (xy<=H2) {  /* promotion */
    xy-=11;
    test = board[xy]->type;
    if (test>0 && test<black) {
      AddBlackMv(xy0,xy,BQUEEN,q,nextf, ((test+WQUEEN-4) << 4)-WPAWN /*mvv lva*/);
      AddBlackMv(xy0,xy,BKNIGHT,q,nextf, ((test+WKNIGHT-4) << 4)-WPAWN);
      AddBlackMv(xy0,xy,BROOK,q,nextf, ((test+WROOK-4) << 4)-WPAWN);
      AddBlackMv(xy0,xy,BBISHOP,q,nextf, ((test+WBISHOP-4) << 4)-WPAWN);
    }
    xy++;
    test = board[xy]->type;
    if (test==0) {
      AddBlackMv(xy0,xy,BQUEEN,q,nextf, (WQUEEN << 4)-WPAWN /*mvv lva*/);
      AddBlackMv(xy0,xy,BKNIGHT,q,nextf, (WKNIGHT << 4)-WPAWN);
      AddBlackMv(xy0,xy,BROOK,q,nextf, (WROOK << 4)-WPAWN);
      AddBlackMv(xy0,xy,BBISHOP,q,nextf, (WBISHOP << 4)-WPAWN);
    }
    xy++;
    test = board[xy]->type;
    if (test>0 && test<black) {
      AddBlackMv(xy0,xy,BQUEEN,q,nextf, ((test+WQUEEN-4) << 4)-WPAWN /*mvv lva*/);
      AddBlackMv(xy0,xy,BKNIGHT,q,nextf, ((test+WKNIGHT-4) << 4)-WPAWN);
      AddBlackMv(xy0,xy,BROOK,q,nextf, ((test+WROOK-4) << 4)-WPAWN);
      AddBlackMv(xy0,xy,BBISHOP,q,nextf, ((test+WBISHOP-4) << 4)-WPAWN);
    }
  } else {
    xy=xy0-11;
    test = board[xy]->type;
    if (test>0 && test<black) {
      AddBlackMv(xy0,xy,BPAWN,q,nextf, (test << 4)-WPAWN /*mvv lva*/);
    } else if (EnPassantSq==xy) {  
      AddBlackMv(xy0,xy,BPAWN,q,nextf, (WPAWN << 4)-WPAWN);/*en passant*/
    }
    xy=xy0-9;
    test = board[xy]->type;
    if (test>0 && test<black) {
      AddBlackMv(xy0,xy,BPAWN,q,nextf, (test << 4)-WPAWN /*mvv lva*/);
    } else if (EnPassantSq==xy) {  
      AddBlackMv(xy0,xy,BPAWN,q,nextf, (WPAWN << 4)-WPAWN); /*en passant*/
    }
  }
}

void AddBlackKingMoves(int xy0, MOVE q[], int *nextf)
{
  register int xy, test;

  xy = xy0 - 11;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  xy++; /* = xy0 - 10;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  xy++; /* = xy0 - 9;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  xy = xy0 + 1;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  xy = xy0 - 1;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  xy = xy0 + 9;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  xy++; /* = xy0 + 10;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  xy++; /* = xy0 + 11;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  } else if (test==0) {
    AddBlackMv(xy0,xy,1,q,nextf,0);
  }
  if ( (gflags&8)==0 /*!bkmoved*/ && xy0==E8) {
    if ( (gflags&32)==0 /*!brh8moved*/ && board[H8]->type==BROOK) {
      if (!BlackKingInCheck() && board[F8]->type==0 && board[G8]->type==0) {
        bking=F8;
        if (!BlackKingInCheck()) {
          AddBlackMv(E8,G8,1,q,nextf,100);
        }
        bking=E8;
      }
    }  
    if ( (gflags&16)==0 /*!bra8moved*/ && board[A8]->type==BROOK) {
      if (!BlackKingInCheck()) {
        if (board[D8]->type==0 && board[C8]->type==0 && board[B8]->type==0) {
          bking=D8;
          if (!BlackKingInCheck()) {
            AddBlackMv(E8,C8,1,q,nextf,90);
          }
          bking=E8;
        }
      }
    }
  }
}

void AddBlackKingCaptures(int xy0, MOVE q[], int *nextf)
{
  register int xy, test;
  xy = xy0 + 1;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 - 1;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 - 11;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 - 10;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 - 9;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
  xy = xy0 + 9;
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 + 10;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
  xy++; /* = xy0 + 11;*/
  test = board[xy]->type;
  if (test>0 && test<black) {
    AddBlackMv(xy0,xy,1,q,nextf,(test << 4)-WKING /*mvv lva*/);
  }
}

int FindAllBlackEvasions(MOVE q[], MOVE qAttacks[], int nA, int nAPieces)
{
  register int test, j;
  int nextfree=0;
  AddBlackKingMoves(Bpieces[0].xy,q,&nextfree);
  if (nAPieces>1) { /* If double check we are done */
    return nextfree;
  }
  for (PIECE *p=Bpieces[0].next; p!=NULL; p=p->next) {
    p->mobility = 0;
    switch (p->type) { 
      case BPAWN  : for (j=0; j<nA; j++) {
                      test = Abs(boardXY[qAttacks[j].m.from] - boardXY[p->xy]);
                      if (test==9 || test==7 || test==8 || test==16 || test==1) {
                        AddBlackPawnCapturesAndPromotions(p->xy, q, &nextfree);
                        AddBlackPawnNonCapsNoProm(p->xy, q, &nextfree);
                        break;
                      }
                    }
                    break;
      case BKNIGHT: for (j=0; j<nA; j++) {
                      test = Abs(boardXY[qAttacks[j].m.from] - boardXY[p->xy]);
                      if (test==10 || test==17 || test==15 || test==6) {
                        AddBlackKnightEvasions(p->xy, q, &nextfree, &(p->mobility), qAttacks, nA);
                        p->mobility -= 4;
                        break;
                      }
                    }
                    break;
      case BBISHOP: for (j=0; j<nA; j++) {
                      test = (boardXY[qAttacks[j].m.from] - boardXY[p->xy]);
                      if (test%9==0 || test%7==0) {
                        AddBlackBishopEvasions(p->xy, q, &nextfree,&(p->mobility), WBISHOP, qAttacks, nA);
                        p->mobility -= 6;
                        break;
                      }
                    }
                    break;
      case BROOK  : AddBlackRookEvasions(p->xy, q, &nextfree, &(p->mobility), WROOK, qAttacks, nA);
                    p->mobility -= 7;
                    break;
      case BQUEEN : AddBlackRookEvasions(p->xy, q, &nextfree, &(p->mobility), WQUEEN, qAttacks, nA);
                    AddBlackBishopEvasions(p->xy, q, &nextfree, &(p->mobility), WQUEEN, qAttacks, nA);
                    p->mobility -= 13;
                    break;
    }
  }
  return nextfree;
}

int FindAllBlackMoves(MOVE q[], int level=-1)
{
  int nextfree=0;
  /* Find Moves plus mobility value for Rooks,Queens,Bishops,Knights. */
  /* Also subtract mobility normalization value */
  for (PIECE *p=Bpieces[0].next; p!=NULL; p=p->next) {
    p->mobility = 0;
    switch (p->type) { 
      case BPAWN  : AddBlackPawnCapturesAndPromotions(p->xy,q,&nextfree);
                    AddBlackPawnNonCapsNoProm(p->xy,q,&nextfree,level);
                    break;
      case BKNIGHT: AddBlackKnightMoves(p->xy,q,&nextfree,&(p->mobility),level);
                    p->mobility -= 4;
                    break;
      case BBISHOP: AddBlackBishopMoves(p->xy,q,&nextfree,&(p->mobility),WBISHOP,level);
                    p->mobility -= 6;
                    break;
      case BROOK  : AddBlackRookMoves(p->xy,q,&nextfree,&(p->mobility),WROOK,level);
                    p->mobility -= 7;
                    break;
      case BQUEEN : AddBlackRookMoves(p->xy,q,&nextfree,&(p->mobility),WQUEEN,level);
                    AddBlackBishopMoves(p->xy,q,&nextfree,&(p->mobility),WQUEEN,level);
                    p->mobility -= 13;
                    break;
    }
  }
  AddBlackKingMoves(Bpieces[0].xy,q,&nextfree);
  /* Sorting left for later during search */
  return nextfree;
}

int FindAllBlackCapturesAndPromotions(MOVE q[])
{
  int nextfree=0;
  /* Find Moves plus mobility value for Rooks,Queens,Bishops,Knights. */
  /* Also subtract mobility normalization value */
  for (PIECE *p=Bpieces[0].next; p!=NULL; p=p->next) {
    p->mobility = 0;
    switch (p->type) { 
      case BPAWN  : AddBlackPawnCapturesAndPromotions(p->xy,q,&nextfree);
                    break;
      case BROOK  : AddBlackRookCaptures(p->xy,q,&nextfree,&(p->mobility),WROOK);
                    p->mobility -= 7;
                    break;
      case BQUEEN : AddBlackRookCaptures(p->xy,q,&nextfree,&(p->mobility),WQUEEN);
                    AddBlackBishopCaptures(p->xy,q,&nextfree,&(p->mobility),WQUEEN);
                    p->mobility -= 13;
                    break;
      case BKNIGHT: AddBlackKnightCaptures(p->xy,q,&nextfree,&(p->mobility));
                    p->mobility -= 4;
                    break;
      case BBISHOP: AddBlackBishopCaptures(p->xy,q,&nextfree,&(p->mobility),WBISHOP);
                    p->mobility -= 6;
                    break;
    }
  }
  AddBlackKingCaptures(Bpieces[0].xy,q,&nextfree);
  qsort(q, nextfree, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
  return nextfree;
}

/* ------------ STATIC EVALUATION FUNCTIONS ------------------------------------- */

int Eval_KingKnightBishop_vs_King(int xy, int BishopSquaresColor)
{
  if (BishopSquaresColor == DarkSq) { 
    if (xy==A1 || xy==H8 || xy==B1 || xy==A2 || xy==H7 || xy==G8) { /* Small triangle */
      return 900;
    } else if (xy==C1 || xy==B2 || xy==A3 || xy==H6 || xy==G7 || xy==F8) { /* middle triangle inner*/
      return 800;
    } else if (xy==D1 || xy==C2 || xy==B3 || xy==A4 || 
               xy==H5 || xy==G6 || xy==F7 || xy==E8) { /* middle triangle outer */
      return 700;
    } else if (xy==E1 || xy==D2 || xy==C3 || xy==B4 || xy==A5 ||
               xy==H4 || xy==G5 || xy==F6 || xy==E7 || xy==D8) {/* big triangle inner */
      return 600;
    } else if (xy==F1 || xy==E2 || xy==D3 || xy==C4 || xy==B5 || xy==A6 ||
               xy==H3 || xy==G4 || xy==F5 || xy==E6 || xy==D7 || xy==C8) {/* big triangle outer*/
      return 500;
    } else { /* add penalty for other cases (middle board or wrong color corner) */
      return -60;
    }
  } else if (BishopSquaresColor == LightSq) { 
    if (xy==H1 || xy==A8 || xy==G1 || xy==H2 || xy==A7 || xy==B8) { /* Small triangle */
      return 900;
    } else if (xy==F1 || xy==G2 || xy==H3 || xy==A6 || xy==B7 || xy==C8) { /* middle triangle inner*/
      return 800;
    } else if (xy==E1 || xy==F2 || xy==G3 || xy==H4 || 
               xy==A5 || xy==B6 || xy==C7 || xy==D8) { /* middle triangle outer */
      return 700;
    } else if (xy==D1 || xy==E2 || xy==F3 || xy==G4 || xy==H5 ||
               xy==A4 || xy==B5 || xy==C6 || xy==D7 || xy==E8) {/* big triangle inner */
      return 600;
    } if (xy==C1 || xy==D2 || xy==E3 || xy==F4 || xy==G5 || xy==H6 ||
          xy==A3 || xy==B4 || xy==C5 || xy==D6 || xy==E7 || xy==F8) {/* big triangle outer*/
      return 500;
    } else {
      return -60;
    }
  } else 
    return 0; /* Should never get here*/
}

int WhiteKnightMiddleGameEval(int xy)
{
 register int kxy=xy, res=0;
 if ((kxy==D5) || (kxy==E5) || (kxy==C5) || (kxy==F5)) {
   res += 2;
 } else if ((kxy==C6) || (kxy==D6) || (kxy==E6) || (kxy==F6)) {
   res += 4;
 }
 return res;
}

int BlackKnightMiddleGameEval(int xy)
{
 register int kxy=xy, res=0;
 if ((kxy==D4) || (kxy==E4) || (kxy==C4) || (kxy==F4)) {
   res -= 2;
 } else if ((kxy==C3) || (kxy==D3) || (kxy==E3) || (kxy==F3)) {
   res -= 4;
 }
 return res;
}

int WhiteKingSafety(int WBishopColor, int BBishopColor, int nof_Queens)
{
  register int xy=wking;
  register int res=0, test;
  if ((gflags&64)==0 /* !WHasCastled */ ) {
    res -= 30;
  }
  test = ColNum[xy];
  if (test==5 || test==4 ) { /* king on files d/e */
    res -= 7;
  } else if ((xy==G1 && board[H1]->type==0) || xy==H1) {
    register int hole1=1;
    register int hole2=1;
    res += 5;
    if (board[F2]->type==WPAWN) {res+=8;}
    if (board[G2]->type==WPAWN) {
      res+=12; hole2=0;
    } else {
      if (board[G2]->type==WBISHOP) {
        res+=8;
      } else if (WBishopColor==DarkSq || WBishopColor==0) {/* fianceto without bishop*/
        res -= 15;
        if (BBishopColor==LightSq || BBishopColor==TwoColor) {
          res -= 35;
        }
      }
    }
    if (board[H2]->type==WPAWN) {res+=10; hole1=0;}
    if (board[H3]->type==WPAWN) {res+=8; hole1=0;}
    if (board[G3]->type==WPAWN) {res+=4; hole2=0;}
    res -= ( (hole1+hole2) << 4 );
  } else if ((xy==C1 && board[B1]->type==0 && board[A1]->type==0) || 
             (xy==B1 && board[A1]->type==0) || 
             (xy==A1)
            ) {
    register int hole1=1;
    register int hole2=1;
    res += 5;
    if (xy==B1 || xy==A1) {res +=1;}
    if (board[C2]->type==WPAWN) {res+=10;}
    if (board[B2]->type==WPAWN) {res+=8; hole2=0;}
    if (board[A2]->type==WPAWN) {res+=4; hole1=0;}
    if (board[A3]->type==WPAWN) {res+=4; hole1=0;}
    res -= ( (hole1+hole2) << 4 );
  } else {
    register int test = xy-9;
    if (board[test]->type==0) res -= 5;
    test--;
    if (board[test]->type==0) res -= 5;
    test--;
    if (board[test]->type==0) res -= 5;
    test = xy+9;
    if (board[test]->type==0) res -= 3;
    test++;
    if (board[test]->type==0) res -= 3;
    test++;
    if (board[test]->type==0) res -= 3;
    if (board[xy+1]->type==0) res -= 3;
    if (board[xy-1]->type==0) res -= 3;
  }
  if (nof_Queens==0) {
    res = res >> 1; /* Without queens , King danger is half */
  }
  return res;
}

int BlackKingSafety(int BBishopColor, int WBishopColor, int nof_Queens)
{
  register int xy=bking;
  register int res=0, test;
  if ((gflags&128)==0 /* !BHasCastled */ ) {
    res += 30;
  }
  test = ColNum[xy];
  if (test==5 || test==4 ) { /* king on files d/e */
    res += 7;
  } else if ((xy==G8 && board[H8]->type==0) || xy==H8) {
    register int hole1=1;
    register int hole2=1;
    res -= 5;
    if (board[F7]->type==BPAWN) {res-=8;}
    if (board[G7]->type==BPAWN) {
      res-=12; hole2=0;
    } else {
      if (board[G7]->type==BBISHOP) {
        res-=8;
      } else if (BBishopColor==LightSq || BBishopColor==0) {/* fianceto without bishop*/
        res += 15;
        if (WBishopColor==DarkSq || WBishopColor==TwoColor) {
          res += 35;
        }
      }
    }
    if (board[H7]->type==BPAWN) {res-=10; hole1=0;}
    if (board[H6]->type==BPAWN) {res-=8; hole1=0;}
    if (board[G6]->type==BPAWN) {res-=4; hole2=0;}
    if (board[F6]->type==BPAWN) {res-=4;}
    res += ( (hole1+hole2) << 4 );
  } else if ((xy==C8 && board[B8]->type==0 && board[A8]->type==0) || 
             (xy==B8 && board[A8]->type==0) || 
             (xy==A8)
            ) {
    register int hole1=1;
    register int hole2=1;
    res -= 5;
    if (xy==B8 || xy==A8) {res -=1;}
    if (board[C7]->type==BPAWN) {res-=8;}
    if (board[B7]->type==BPAWN) {res-=12; hole2=0;}
    if (board[A7]->type==BPAWN) {res-=10; hole1=0;}
    if (board[A6]->type==BPAWN) {res-=8; hole1=0;}
    res += ( (hole1+hole2) << 4 );
  } else {
    register int test = xy-9;
    if (board[test]->type==0) res += 5;
    test--;
    if (board[test]->type==0) res += 5;
    test--;
    if (board[test]->type==0) res += 5;
    test = xy+9;
    if (board[test]->type==0) res += 3;
    test++;
    if (board[test]->type==0) res += 3;
    test++;
    if (board[test]->type==0) res += 3;
    if (board[xy+1]->type==0) res += 3;
    if (board[xy-1]->type==0) res += 3;
  }
  if (nof_Queens==0) {
    res = res >> 1; /* Without queens, King danger is half */
  }
  return res;
}
  
int StaticEval(int * EnoughMaterial)
{
  register int i, j, xy, ret=0, WhitePieces=0, BlackPieces=0, xy0, Passed, isolated;
  register int queens=0, rooks=0, Wbishops=0, Wknights=0, Bbishops=0, Bknights=0, wpawns=0, bpawns=0, allpawns=0;
  register int WBishopColor=0, BBishopColor=0; /*0: No bishop, 1:LightSq, 2:DarkSq, 3:Both */
  register int IsAlmostCentered=0, IsBoardEdge=0, IsCentralized=0;
  int KingHaltsPassed=0, MiddleGame=0;
  int Wisolani=0, Bisolani=0;
  register unsigned int Indx;
  int pawnHashHit=0, extra_pawn_val=0;

  *EnoughMaterial = -1;
  ret = move_stack[mv_stack_p].material;

  for (PIECE *p=Wpieces[0].next; p!=NULL; p=p->next) {
    WhitePieces++;
    switch (p->type) {
       case WPAWN  : 
         wpawns++;
         ret += W_Pawn_E[p->xy];
         break;
       case WROOK  : 
         ret += p->mobility;
         rooks++;
         break;
       case WKNIGHT: 
         ret += p->mobility;
         ret += KnightE[p->xy];
         Wknights++;
         break;
       case WBISHOP: 
         ret += p->mobility;
         Wbishops++;
         WBishopColor += BishopSquareColor[WhiteSq[p->xy]];
         break;
       case WQUEEN : 
         ret += p->mobility;
         queens++;
         break;
    }
  }
  for (PIECE *p=Bpieces[0].next; p!=NULL; p=p->next) {
    BlackPieces++;
    switch (p->type) { 
       case BPAWN  : 
         bpawns++;
         ret += B_Pawn_E[p->xy];
         break;
       case BROOK  : 
         ret -= p->mobility; 
         rooks++;
         break;
       case BKNIGHT: 
         ret -= p->mobility; 
         ret -= KnightE[p->xy];
         Bknights++;
         break;
       case BBISHOP: 
         ret -= p->mobility;
         Bbishops++;
         BBishopColor += BishopSquareColor[WhiteSq[p->xy]];
         break;
       case BQUEEN : 
         ret -= p->mobility;
         queens++;
        break;
    }
  }
  allpawns = wpawns+bpawns;
  /* Depending on number of pawns, add bonus for 2 bishops .. small bonus for 2 knights*/
  if (allpawns<15) {
    if (Wbishops==2) ret += 35;
    if (Bbishops==2) ret -= 35;
  } else {
    if (Wbishops==2) ret += 18;
    if (Bbishops==2) ret -= 18;
  }
  if (Wknights==2) ret += 10;
  if (Bknights==2) ret -= 10;
  /* End of 1st pass */
  /* include kings in piece number */
  WhitePieces++;
  BlackPieces++;
  Pieces= WhitePieces + BlackPieces;
  *EnoughMaterial = Pieces - allpawns;
  if ((Pieces<4 || (Pieces==4 && Wbishops==1 && WBishopColor==BBishopColor)) && (allpawns==0) && (queens==0) && (rooks==0)) {
    *EnoughMaterial = 0;
    return 0;
  }
  MiddleGame = (!(Pieces < 20 && (rooks<4 || Pieces<13) && (queens<2 || Pieces<13 || (Pieces-allpawns<7))) );
  if (MiddleGame) {
    if (ret>250 || ret<-250)
      return ret;
  }
  unsigned long long pawnkey = move_stack[mv_stack_p].PawnHash;
  Indx = pawnkey & PMAX_TT;
  register struct ptt_st *ptte = &P_T_T[Indx];

  if (ptte->PawnHash == pawnkey) {
    pawnHashHit = 1;
    extra_pawn_val = ptte->value;
  } else {
   /* evaluation for isolated white pawns*/
   for (i=8; i<16; i++) { 
    xy = Wpieces[i].xy;
    if (xy==0) 
      continue;
    if (Wpieces[i].type!=WPAWN) 
      continue;
    isolated=1;
    for (j=8; j<16; j++) {
      if (i==j)
        continue;
      xy0 = Wpieces[j].xy;
      if (xy0==0) 
        continue;
      if (Wpieces[j].type!=WPAWN) 
        continue;

      if (HaveNeighborColummns(xy,xy0)) {
        isolated=0;
        break;
      }
    }
    if (isolated) {
      Wisolani++;
      extra_pawn_val -= 10;
    }
   }
   for (i=8; i<16; i++) { /* evaluation for isolated black pawns*/
    xy = Bpieces[i].xy;
    if (xy==0) 
      continue;
    if (Bpieces[i].type!=BPAWN) 
      continue;
    isolated=1;
    for (j=8; j<16; j++) {
      if (i==j)
        continue;
      xy0 = Bpieces[j].xy;
      if (xy0==0) 
        continue;
      if (Bpieces[j].type!=BPAWN) 
        continue;
      if (HaveNeighborColummns(xy,xy0)) {
        isolated=0;
        break;
      }
    }
    if (isolated) {
      Bisolani++;
      extra_pawn_val += 10;
    }
   }
   /* 2nd pass - Middle game / endgame evaluation */
   /* second pass evaluation for passed pawns*/
   for (i=8; i<16; i++) { 
    xy = Wpieces[i].xy;
    if (xy==0) 
      continue;
    if (Wpieces[i].type!=WPAWN) 
      continue;
    Passed = 1;
    for (xy0=xy+10; xy0<=H7; xy0+=10) {
      if (board[xy0]->type==BPAWN || board[xy0-1]->type==BPAWN || board[xy0+1]->type==BPAWN) {
        Passed=0;
        break;
      }
    }
    if (Passed) { /*for pawns mobility means passed pawn*/
      Wpieces[i].mobility = 2;
      if (xy >= A4) Wpieces[i].mobility += 8;
      if (xy >= A5) Wpieces[i].mobility += 12;
      if (xy >= A6) Wpieces[i].mobility += 16;
      if (board[xy-9]->type==WPAWN || board[xy-11]->type==WPAWN)
        Wpieces[i].mobility += (Wpieces[i].mobility >> 1); /*supported passed pawn bonus*/
    }
    if (xy >= A7)  Wpieces[i].mobility += 20;  
    extra_pawn_val += Wpieces[i].mobility;
   }
   for (i=8; i<16; i++) {
    xy = Bpieces[i].xy;
    if (xy==0) 
      continue;
    if (Bpieces[i].type!=BPAWN) 
      continue;
    Passed = 1;
    for (xy0=xy-10; xy0>=A2; xy0-=10) {
      if (board[xy0]->type==WPAWN || board[xy0-1]->type==WPAWN || board[xy0+1]->type==WPAWN) {
        Passed=0;
        break;
      }
    }
    if (Passed) { 
      Bpieces[i].mobility = 2;
      if (xy<=H5) Bpieces[i].mobility += 8;
      if (xy<=H4) Bpieces[i].mobility += 12;
      if (xy<=H3) Bpieces[i].mobility += 16;
      if (board[xy+9]->type==BPAWN || board[xy+11]->type==BPAWN)
        Bpieces[i].mobility += (Bpieces[i].mobility>>1);/*supported passed pawn bonus*/
    }
    if (xy<=H2)  Bpieces[i].mobility += 20;
    extra_pawn_val -= Bpieces[i].mobility;
   }
  }

  if (MiddleGame) {
    ret += extra_pawn_val;
    /* Knights*/
    xy = Wpieces[6].xy;
    if (xy!=0) {
      if (xy==G1) {
        ret -= 7;
      } else ret += WhiteKnightMiddleGameEval(xy);
    }
    xy = Wpieces[7].xy;
    if (xy!=0) {
      if (xy==B1) {
        ret -= 7;
      } else ret += WhiteKnightMiddleGameEval(xy);
    }
    xy = Bpieces[6].xy;
    if (xy!=0) {
      if (xy==G8) {
        ret += 7;
      } else ret += BlackKnightMiddleGameEval(xy);
    }
    xy = Bpieces[7].xy;
    if (xy!=0) {
      if (xy==B8) {
        ret += 7;
      } else ret += BlackKnightMiddleGameEval(xy);
    }
    /* Bishops */
    if (Wpieces[4].xy==F1)
      ret -= 5;
    if (Wpieces[5].xy==C1)
      ret -= 5;
    if (Bpieces[4].xy==F8)
      ret += 5;
    if (Bpieces[5].xy==C8)
      ret += 5;
    /* Central Squares Control */
    i=board[E4]->type;
    if (i>0) {
     if (i>black) {
      ret -= 5;
     } else {
      ret += 5;
     }
    }
    i=board[D4]->type;
    if (i>0) {
     if (i>black) {
      ret -= 5;
     } else {
      ret += 5;
     }
    }
    i=board[E5]->type;
    if (i>0) {
     if (i>black) {
      ret -= 5;
     } else {
      ret += 5;
     }
    }
    i=board[D5]->type;
    if (i>0) {
     if (i>black) {
      ret -= 5;
     } else {
      ret += 5;
     }
    }
    /* Kings safety */
    ret += BlackKingSafety(BBishopColor, WBishopColor,queens);
    ret += WhiteKingSafety(WBishopColor, BBishopColor,queens);
  } else {  /* Endgame Eval */
    int ThreeOrFourPiecesNopawns = (Pieces < 5) && (allpawns==0);
    int SpecialforBasicEndgames = (LoneKingReachedEdge && ThreeOrFourPiecesNopawns);
    if (!pawnHashHit) {
     int MaxPassedConnected;
     /*Add a penalty for no pawns at endgame*/
     if (wpawns==0)
       extra_pawn_val -= 50;
     if (bpawns==0)
       extra_pawn_val += 50;
     /* Add or subtract extra bonus/malus for endgame isolated pawns */
     if (Wisolani) {
       extra_pawn_val -= (Wisolani<<3);
       if (Wisolani>2) 
         extra_pawn_val -= (Wisolani<<3);
     }
     if (Bisolani) {
       extra_pawn_val += (Bisolani<<3);
       if (Bisolani>2) 
         extra_pawn_val += (Bisolani<<3);
     }
     /* endgame adjustments for white passed pawns */
     MaxPassedConnected=0;
     for (i=8; i<16; i++) {
       xy = Wpieces[i].xy;
       if (xy==0) 
         continue;
       if (Wpieces[i].type!=WPAWN) 
         continue;
       if (Wpieces[i].mobility==0) 
         continue;
       extra_pawn_val += Wpieces[i].mobility;
       if (i>8) {
         xy0 = Wpieces[i-1].xy;
         if (xy0!=0) {
           if (Wpieces[i-1].type==WPAWN && Wpieces[i-1].mobility!=0) {
             if ( RowNum[xy]>3 && RowNum[xy0]>3 && HaveNeighborColummns(xy,xy0) ) {
               Passed = (RowNum[xy] + RowNum[Wpieces[i-1].xy]) << 3; /* White advanced connected passed pawn bonus */
               if (Passed > MaxPassedConnected)
                 MaxPassedConnected = Passed;
             } 
           }
         }
       }
     }
     extra_pawn_val += MaxPassedConnected;
     /* endgame adjustments for black passed pawns */
     MaxPassedConnected=0;
     for (i=8; i<16; i++) { 
       xy = Bpieces[i].xy;
       if (xy==0) 
         continue;
       if (Bpieces[i].type!=BPAWN) 
         continue;
       if (Bpieces[i].mobility==0) 
         continue;
       extra_pawn_val -= Bpieces[i].mobility;
       if (i>8) {
         xy0 = Bpieces[i-1].xy;
         if (xy0!=0) {
           if (Bpieces[i-1].type==BPAWN && Bpieces[i-1].mobility!=0) {
             if (RowNum[xy]<6 && RowNum[xy0]<6 && HaveNeighborColummns(xy,xy0) ) {
               Passed = (18 - RowNum[xy] - RowNum[Bpieces[i-1].xy]) << 3; /* Black advanced connected passed pawn bonus */
               if (Passed > MaxPassedConnected)
                 MaxPassedConnected = Passed;
             }
           }
         }
       }
     }
     extra_pawn_val -= MaxPassedConnected;
    }
    ret += extra_pawn_val;
    /* White King special endgame evaluation */
    xy = wking;
    if (SpecialforBasicEndgames && (queens==0) && (rooks==0) && 
        (BBishopColor == DarkSq || BBishopColor == LightSq)) 
    { /* K+N+B vs K */
      ret -= Eval_KingKnightBishop_vs_King(xy, BBishopColor);
    } else {
      int BasicEndGames = (ThreeOrFourPiecesNopawns && (WhitePieces==1));

      if (SpecialforBasicEndgames && BlackPieces==1) {
        ret -= Abs(RowNum[wking] - RowNum[bking]) + Abs(ColNum[wking] - ColNum[bking]);
      }
      IsCentralized    = Central[xy];
      IsAlmostCentered = PartCen[xy];
      if (Pieces==3 && bpawns==1) 
      {/* special for king+pawn endgames */
        Passed = 1;
        for (xy0=xy+10; xy0<=H7; xy0+=10) {
          if (board[xy0]->type==BPAWN) {
            Passed=0;
            break;
          }
        }
        if (!Passed && xy0-xy<21) {
          return 0;
        }
      }
      if (Pieces==5 && rooks==2 && bpawns==1 && wpawns==0) 
      {/* special for rook+pawn endgames */
         KingHaltsPassed=1;
      }
      if (IsCentralized) { /* Centralized King */
        if (!KingHaltsPassed) ret += 40;
        if (BasicEndGames) ret -= 25;
      } else if (IsAlmostCentered) { /* Partially Centralized King */
        if (!KingHaltsPassed) ret += 20;
        if (BasicEndGames) ret -= 15;
      } else if (PartEdg[xy]) { /* King almost on edge */
         if (!KingHaltsPassed) ret -= 7;
         if (BasicEndGames) {
           if (xy==B2 || xy==G2 || xy==B7 || xy==G7) { /* Penalty for almost edge corners */
             ret -= 150;
           } else if (xy==C2 || xy==F2 || xy==B3 || xy==G3 || xy==B6 || xy==C7 || xy==F7 || xy==G6) {
             /* smaller penalty for closer to center*/
             ret -=80;
           }
         }
      } else /*if (IsBoardEdge)*/ { /* king on Edge */
        if (KingHaltsPassed) {
          ret -= 10;
        } else {
          ret -= 30;
        }
        if (BasicEndGames) {
          ret -= 300;
          if ((queens==0) && (rooks==0)) { 
            if ((BBishopColor == 0) || (BBishopColor == TwoColor)) { /* K+B+B vs K or K+N+N vs K*/
              if (xy==D1 || xy==E1 || xy==H4 || xy==H5 || xy==A4 || xy==A5 || xy==D8 || xy==E8 ) 
              { /* Away from corner */
                ret += 120;
              } else if (xy==C1 || xy==F1 || xy==H3 || xy==H6 || xy==A3 || xy==A6 || xy==C8 || xy==F8 ) 
              { /* Partially cornered*/
                ret -= 10;
              } else if (xy==A1 || xy==H1 || xy==A8 || xy==H8 || xy==B1 || xy==G1 || 
                         xy==H2 || xy==H7 || xy==A2 || xy==A7 || xy==B8 || xy==G8) 
              { /* cornered */
                ret -= 120;
              }
            } 
          } 
        }
      }
    }
    /* Black King special endgame evaluation */
    xy = bking;
    KingHaltsPassed = 0;
    if (SpecialforBasicEndgames && (queens==0) && (rooks==0) &&
        (WBishopColor == DarkSq || WBishopColor == LightSq)) 
    { /* K+N+B vs K */
      ret += Eval_KingKnightBishop_vs_King(xy, WBishopColor);
    } else {
      int BasicEndGames = (ThreeOrFourPiecesNopawns && (BlackPieces==1));
      if (SpecialforBasicEndgames && WhitePieces==1) {
        ret += Abs(RowNum[wking] - RowNum[bking]) + Abs(ColNum[wking] - ColNum[bking]);
      }
      /*IsBoardEdge      = Edge[xy];*/
      IsCentralized    = Central[xy];
      IsAlmostCentered = PartCen[xy];
      if (Pieces==5 && rooks==2 && wpawns==1 && bpawns==0) 
      {/* special for rook+pawn endgames */
         KingHaltsPassed=1;
      }
      if (Pieces==3 && wpawns==1) 
      {/* special for king+pawn endgames */
        Passed = 1;
        for (xy0=xy-10; xy0>=A2; xy0-=10) {
          if (board[xy0]->type==WPAWN) {
            Passed=0;
            break;
          }
        }
        if (!Passed && xy-xy0<21) {
          return 0;
        }
      }
      if (IsCentralized) { 
        if (!KingHaltsPassed) ret -= 40;
        if (BasicEndGames) ret += 25;
      } else if (IsAlmostCentered) { 
        if (!KingHaltsPassed) ret -= 20;
        if (BasicEndGames) ret += 15;
      } else if (PartEdg[xy]) { /* King almost on edge */
        if (!KingHaltsPassed) ret += 7;
        if (BasicEndGames) {
          if (xy==B2 || xy==G2 || xy==B7 || xy==G7) { /* Penalty for almost edge corners */
            ret += 150;
          } else if (xy==C2 || xy==F2 || xy==B3 || xy==G3 || xy==B6 || xy==C7 || xy==F7 || xy==G6) {
            /* smaller penalty for closer to center*/
            ret +=80;
          }
        }
      } else /*if (IsBoardEdge)*/ { /* king on Edge */
        if (KingHaltsPassed) {
          ret+=10;
        } else {
          ret += 30;
        }
        if (BasicEndGames) {
          ret += 300;
          if ((queens==0) && (rooks==0)) { 
            if ((WBishopColor == 0) || (WBishopColor == TwoColor)) { /* K+B+B vs K or K+N+N vs K*/
              if (xy==D1 || xy==E1 || xy==H4 || xy==H5 || xy==A4 || xy==A5 || xy==D8 || xy==E8 ) 
              { /* Away from corner */
                ret -= 120;
              } else if (xy==C1 || xy==F1 || xy==H3 || xy==H6 || xy==A3 || xy==A6 || xy==C8 || xy==F8 ) 
              { /* Partially cornered*/
                ret += 10;
              } else if (xy==A1 || xy==H1 || xy==A8 || xy==H8 || xy==B1 || xy==G1 || 
                         xy==H2 || xy==H7 || xy==A2 || xy==A7 || xy==B8 || xy==G8) 
              { /* cornered */
                ret += 120;
              }
            } 
          } 
        }
      }
    }
  }
  if (!pawnHashHit) {
    ptte->PawnHash = pawnkey;
    ptte->value = extra_pawn_val;
  }
  return ret;
}

/* ------------------ BOOK FUNCTIONS ------------------------------------ */
  
int IsBookLine(int *BookLineNoP, MOVE movelst[], int moves, int color) 
{
 int i, j, matchfound=0, level, CheckForBadMove, QuestionMarksFound;
 MOVE Am;
 static char bline[1024]={"e2e4 e7e5 g1f3 b8c6 f1c4\n"}; /* Internal 1 line Book ! */
 int matched=0;
 char *cp;
 if (NotStartingPosition)
   return 0;
 *BookLineNoP=-1;
 if (book_file==NULL)  { /* if extenal book file is missing use internal bline[] book */
  matchfound = 1;
  QuestionMarksFound = 0;
    level = 1;
  for (j = 0; j < strlen(CurrentLine); j++) {
    if (bline[j]=='?') {
      cp = &bline[j+1];
      QuestionMarksFound++;
    } else {
      cp = &bline[j];
    }
    if ((*cp) == ' ')
      level++;
        
    if ((*cp) == '\0' || (*cp) != CurrentLine[j])
      matchfound = 0;
  }
  if (matchfound==1) {
    /* parse the book move that continues the line */
    CheckForBadMove=0;
    if (color==white) {
      if (level%2==1)
        CheckForBadMove=1;
    } else {
      if (level%2==0)
        CheckForBadMove=1;
    }
    if (!ParsePlayerMove(&bline[strlen(CurrentLine)+QuestionMarksFound], &Am, CheckForBadMove)) {
      matchfound =0;
    } else {
      /* printf("\n--Matched--%s--\n",bline);*/
       for (i=0; i<moves; i++) {  /* for every move */
        if (movelst[i].m.from==Am.m.from  &&
            movelst[i].m.to==Am.m.to  &&
            movelst[i].m.flag==Am.m.flag  
            ) 
        {
          MatchingBookMoves[matched] = i;
          if (matched<MAX_BOOK_MATCH) 
            matched++;
        }
      }
    }
  }
 } else {
  fseek(book_file, 0, SEEK_SET);
  while (fgets(bline, 1024, book_file)) {
    matchfound = 1;
    QuestionMarksFound = 0;
    level = 1;
    for (j = 0; j < strlen(CurrentLine); j++) {
      if (bline[j]=='?') {
        cp = &bline[j+1];
        QuestionMarksFound++;
      } else {
        cp = &bline[j];
      }
      if ((*cp) == ' ')
        level++;
        
      if ((*cp) == '\0' || (*cp) != CurrentLine[j])
        matchfound = 0;
    }
    if (matchfound==1) {
      /* parse the book move that continues the line */
      CheckForBadMove=0;
      if (color==white) {
        if (level%2==1)
          CheckForBadMove=1;
      } else {
        if (level%2==0)
          CheckForBadMove=1;
      }
      if (!ParsePlayerMove(&bline[strlen(CurrentLine)+QuestionMarksFound], &Am, CheckForBadMove)) {
        matchfound =0;
      } else {
        /* printf("\n--Matched--%s--\n",bline);*/
        for (i=0; i<moves; i++) {  /* for every move */
          if (movelst[i].m.from==Am.m.from  &&
              movelst[i].m.to==Am.m.to  &&
              movelst[i].m.flag==Am.m.flag  
              ) 
          {
            MatchingBookMoves[matched] = i;
            if (matched<MAX_BOOK_MATCH) 
              matched++;
          }
        }
      }
    }
  }
 }
  if (matched==0) {
    NotStartingPosition=1;
    return 0;
  }
  if (matched==1) {
    *BookLineNoP = MatchingBookMoves[0];
  } else {
    int r=rand();
    int Secs=GetMillisecs()/1000;
    while (Secs < 0) {
      Secs = Secs % 100000;
      Secs = - Secs;
    }
    while (r < 0) {
      r = r % 1000;
      r = - r;
    }
    j = ((Secs%100000) * (r%1000)) % matched;
    *BookLineNoP = MatchingBookMoves[j];
  }
  return 1;  
}

/* ----------------- MAIN SEARCH FUNCTIONS ------------------------------------- */

void StartingPosition(void)
{
  int i;
  EmptyBoard();
  board[A1]=&Wpieces[2]; Wpieces[2].xy=A1;
  board[H1]=&Wpieces[3]; Wpieces[3].xy=H1; /* WROOKS */
  board[A8]=&Bpieces[2]; Bpieces[2].xy=A8;
  board[H8]=&Bpieces[3]; Bpieces[3].xy=H8; /* BROOKS */
  board[G1]=&Wpieces[6]; Wpieces[6].xy=G1;
  board[B1]=&Wpieces[7]; Wpieces[7].xy=B1; /* WKNIGHTS */
  board[G8]=&Bpieces[6]; Bpieces[6].xy=G8;
  board[B8]=&Bpieces[7]; Bpieces[7].xy=B8; /* BKNIGHTS */
  board[F1]=&Wpieces[4]; Wpieces[4].xy=F1;
  board[C1]=&Wpieces[5]; Wpieces[5].xy=C1; /* WBISHOPS */
  board[F8]=&Bpieces[4]; Bpieces[4].xy=F8;
  board[C8]=&Bpieces[5]; Bpieces[5].xy=C8; /* BBISHOPS */
  board[D1]=&Wpieces[1]; Wpieces[1].xy=D1; /* WQUEEN */
  board[D8]=&Bpieces[1]; Bpieces[1].xy=D8; /* BQUEEN */
  board[E1]=&Wpieces[0]; Wpieces[0].xy=E1; /* WKING */
  board[E8]=&Bpieces[0]; Bpieces[0].xy=E8; /* BKING */
  for (i=0; i<8; i++) {
    board[i+A2]= &Wpieces[i+8]; Wpieces[i+8].xy=i+A2; /* WPAWNS */
    board[i+A7]= &Bpieces[i+8]; Bpieces[i+8].xy=i+A7; /* BPAWNS */
  }
  /* castling flags reset*/  
  gflags = 0; /*  wra1moved=wrh1moved=wkmoved=bra8moved=brh8moved=bkmoved=0;  WHasCastled=0;  BHasCastled=0;*/
  EnPassantSq=0;  
  /* Move Stack Pointers reset */
  cst_p=0;
  mv_stack_p=0;
  HalfMovesPlayed=0;
  CurrentLine[0] = '\0';
  LoneKingReachedEdge=0;
  FiftyMoves=0;
  NotStartingPosition = 0;
  PlayerMove.u=0;
}

int MoveIsValid(MOVE Key, MOVE q[], int qsize)
{ 
  register unsigned int j;
  if (Key.u) {
    for (j=0; j<qsize; j++) {
      if (q[j].m.from==Key.m.from && q[j].m.to==Key.m.to && q[j].m.flag==Key.m.flag) {
        return 1;
      }
    }
  }
  return 0;
}

int FindAndUpdateInPlace(MOVE mlp[], int lSize, MOVE Key, int place)
{
  register int j, f=0;
  if (Key.u) {
    int utemp;
    if (mlp[place].m.from==Key.m.from  && mlp[place].m.to==Key.m.to) 
      return 1;
    for (j=0; j<lSize; j++) {
      if (j==place)
        continue;
      if (mlp[j].m.from==Key.m.from  && mlp[j].m.to==Key.m.to) {
        f=1;
        utemp = mlp[j].u;
        break;
      }
    }
    if (f) {
      mlp[j].u = mlp[place].u;
      mlp[place].u = utemp;
    }
  }
  return f;
}

void OutputDanger(int depth, int score, MOVE *defenseP)
{
  if (Xoutput==_XBOARD_OUTPUT) {
    printf("%d %d %d %d ", depth, score, (GetMillisecs() - start_time) / 10, nodes);
    printf("%s? ",TranslateMoves(&GlobalPV.argmove[0]));
    printf(" %s! \n", TranslateMoves(defenseP));
    fflush(stdout);
  } else if (Xoutput==_NORMAL_OUTPUT) {
    printf("   %7.2lf%7.2lf   ",0.01*score, SECONDS_PASSED);
    printf("%s? ",TranslateMoves(&GlobalPV.argmove[0]));
    printf(" %s! \n", TranslateMoves(defenseP));
  }
}

int Quiescence(int alpha, int beta, int color)
{
  register int e, score, i, m, NextColor, delta_1;
  int IsMaterialEnough;
  MOVE movelst[MAXMV];
  nodes++;
  if (color==black) {
    e = -StaticEval(&IsMaterialEnough);
    if (IsMaterialEnough==0)
      return 0;
    e += (mv_stack_p - Starting_Mv);
    if( e >= beta )
      return beta;
    if (mv_stack_p - Starting_Mv > MAX_DEPTH ) {
      return e;
    }
    delta_1 = QUEEN_V + PAWN_V;
    if ( move_stack[mv_stack_p].special == PROMOT ) {
      delta_1 += QUEEN_V - PAWN_V;
    }
    if ( (e+delta_1) < alpha ) {
      return alpha;
    }
    if( alpha < e )
      alpha = e;
    m=FindAllBlackCapturesAndPromotions(movelst);
    if (m==0)
      return e;
    NextColor = white;
  } else {
    e = StaticEval(&IsMaterialEnough);
    if (IsMaterialEnough==0)
      return 0;
    e -= (mv_stack_p - Starting_Mv);
    if( e >= beta )
      return beta;
    if (mv_stack_p - Starting_Mv > MAX_DEPTH ) {
      return e;
    }
    delta_1 = QUEEN_V + PAWN_V;
    if ( move_stack[mv_stack_p].special == PROMOT ) {
      delta_1 += QUEEN_V - PAWN_V;
    }
    if ( (e+delta_1) < alpha ) {
      return alpha;
    }
    if( alpha < e )
      alpha = e;
    m=FindAllWhiteCapturesAndPromotions(movelst);
    if (m==0)
      return e;
    NextColor = black;
  }
  for (i=0; i<m; i++) {
    if ( (e + PieceValFromType[board[movelst[i].m.to]->type] + DELTAMARGIN) < alpha ) {
      continue;
    }
    PushStatus();
    MakeMove(&movelst[i]);
    if (color==black) {
      if (BlackKingInCheck()) {
        RetractLastMove();
        PopStatus();
        continue;
      }
    } else {
      if (WhiteKingInCheck()) {
        RetractLastMove();
        PopStatus();
        continue;
      }
    }
    score =  - Quiescence(-beta, -alpha, NextColor);
    RetractLastMove();
    PopStatus();
    if( score >= beta ) {
      return beta;
    }
    if( score > alpha ) {
      alpha = score;
    }
  }
  return alpha;
}

int Negalight(int depth, int alpha, int beta, int color)
{
  if (depth==0) 
  { /* terminal node  */
    return Quiescence(alpha, beta, color);
  } 
  else 
  {
    register int i;
    int x, n2=-1, NextColor, actual=0;
    MOVE m2lst[MAXMV];
    if (color==white) {
      n2 = FindAllWhiteMoves(m2lst);
      qsort(m2lst, n2, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
      NextColor = black;
    } else {
      n2 = FindAllBlackMoves(m2lst);
      qsort(m2lst, n2, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
      NextColor = white;
    }
    for (i=0; i<n2; i++) {
      PushStatus();
      MakeMove(&m2lst[i]);
      if (color==black) {
        if (BlackKingInCheck()) {
          RetractLastMove();
          PopStatus();
          continue;
        }
      } else {
        if (WhiteKingInCheck()) {
          RetractLastMove();
          PopStatus();
          continue;
        }
      }
      x =  - Negalight(depth-1, -beta, -alpha, NextColor);
      RetractLastMove();
      PopStatus();
      if (x>alpha) {
        alpha = x;
      }
      if (alpha>=beta) {
        return alpha;
      }
      actual++;
    }/* for each node */
    if (actual==0) {
      if (color==white) {
        if (WhiteKingInCheck()) {/* Mate */
          return -INFINITY_ + (mv_stack_p - Starting_Mv);
        } else {/* StaleMate */
          return 0;
        }
      } else {
        if (BlackKingInCheck()) {/* Mate */
          return -INFINITY_ + (mv_stack_p - Starting_Mv);
        } else {/* StaleMate */
          return 0;
        }
      }
    }
    return alpha;
  }
}

void Internal_Iterative_Deepening(MOVE q[], int n, int Nextcolor, int depth, int IID_a, int IID_b)
{
  register int i, utemp, maxi=-1, t_score;
  for (i=0; i<n; i++) {
    if (q[i].m.flag!=0) { /* If is legal move */
      PushStatus();
      MakeMove(&q[i]);
      t_score = - Negalight(depth-1, -IID_b, -IID_a, Nextcolor);
      RetractLastMove();
      PopStatus();
      if (t_score>IID_a) {
        IID_a = t_score;
        maxi = i;
        if (IID_a>=IID_b)
          break;
      }
    }
  }
  if (maxi>=0) {
    utemp = q[maxi].u;
    q[maxi].u = q[0].u;
    q[0].u = utemp;
  }
  return;
}

int FutilityPruning(int depth, int eval, int alpha) 
{
  if (depth < FUTIL_DEPTH) {
    if ( FutilityMargins[depth] + eval < alpha ) {
      return 1;
    }
  }
  return 0;
}

int ReverseFutilityPruning(int depth, int eval, int beta) 
{
  if (depth < FUTIL_DEPTH) {
    if (eval - FutilityMargins[depth] >= beta) {
      return 1;
    }
  }
  return 0;
}

/* -------------------------------- NEGA SCOUT ALGORITHM -------------------------------- */

int NegaScout(int CanNull, int level, LINE * pline, MOVE mlst[], int n, int depth, int alpha, int beta, int color, 
              int *bestMoveIndex, int IsPVnode, int BeingInCheck, MOVE * ThreatP, int FollowingPV)
{
  register int i, e, t, x, a, w2=-1, b2=-1, NextDepth, NextColor, ngmoves=0, nChecks, CanReduct, CurrMoveFollowsPV;
  int iret=0, IsMaterialEnough, iretNull=-1, legality_checked=0, nCheckPieces, LastMoveToSquare, LastMovePieceType;
  int IID_d, ShouldIID=1, TT_value, NullDepth;
  MOVE w2movelst[MAXMV], b2movelst[MAXMV], CheckAttacks[MAXMV];
  LINE line;
  MOVE Tbest, NullBest, HashBest, *GPVmp;

  pline->cmove = 0;
  *bestMoveIndex = TERMINAL_NODE;
  HashBest.u=0;
  if (depth==0)
  { /*node is a terminal node  */
    return Quiescence(alpha, beta, color);
  } 
  else 
  {
    nodes++;
    if (mv_stack_p - Starting_Mv > MAX_DEPTH ) { /* We are too deep */
      return Quiescence(alpha, beta, color);
    }
    /* Check Transposition Table for a match */
    if (!IsPVnode) {
     if (level&1) { /* Our side to move */
      if (Check_TT(T_T, alpha, beta, depth, move_stack[mv_stack_p].PositionHash, &TT_value, &HashBest)) {
        *bestMoveIndex = TERMINAL_NODE;
        pline->argmove[0].u = HashBest.u;
        pline->cmove = 1;
        return TT_value;
      }
     } else { /* Opponent time to move */
      if (Check_TT(Opp_T_T, alpha, beta, depth, move_stack[mv_stack_p].PositionHash, &TT_value, &HashBest)) {
        *bestMoveIndex = TERMINAL_NODE;
        pline->argmove[0].u = HashBest.u;
        pline->cmove = 1;
        return TT_value;
      }
     }
    } else if (level>1) {
     if (level&1) { /* Our side to move */
      if (Check_TT_PV(T_T, depth, move_stack[mv_stack_p].PositionHash, &TT_value, &HashBest)) {
        *bestMoveIndex = TERMINAL_NODE;
        pline->argmove[0].u = HashBest.u;
        pline->cmove = 1;
        return TT_value;
      }
     } else { /* Opponent time to move */
      if (Check_TT_PV(Opp_T_T, depth, move_stack[mv_stack_p].PositionHash, &TT_value, &HashBest)) {
        *bestMoveIndex = TERMINAL_NODE;
        pline->argmove[0].u = HashBest.u;
        pline->cmove = 1;
        return TT_value;
      }
     }
    }
    e = StaticEval(&IsMaterialEnough);
    if (color==black) {
      e = -e;
      NextColor = white;
    } else {
      NextColor = black;
    }
    if (!BeingInCheck) { /* Can do pruning here */
      if (IsMaterialEnough>7 && !IsPVnode) { /* Reverse Futility Pruning */
        if (((int)move_stack[mv_stack_p].move.m.mvv_lva < TACTICAL_MARGIN)) {
          if ( ReverseFutilityPruning(depth, e, beta) ) {
            *bestMoveIndex = TERMINAL_NODE;
            return e;
          }
        }
      }
      /* Adaptive Null Move Pruning */
      NullBest.u = 0;
      NullDepth = THREAT_DEPTH;
      if (depth > ADAPT_NULL_LIMIT) {
        NullDepth++;
      }
      if (CanNull && (depth > NullDepth) && (IsMaterialEnough > 5)) {
        NextDepth = depth-1-NullDepth;
        if (color==black) {
          if (NextDepth==0) {
            w2=0;
          } else {
            w2=FindAllWhiteMoves(w2movelst, level);
            qsort(w2movelst, w2, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
          }
          x =  - NegaScout(0, level+1, &line, w2movelst, w2, NextDepth, -beta, -alpha /*-beta+1*/, NextColor, &iretNull, IsPVnode, 0, NULL,0);
          if (iretNull>=0) {
            NullBest.u = w2movelst[iretNull].u;
          }
        } else {
          if (NextDepth==0) {
            b2=0;
          } else {
            b2=FindAllBlackMoves(b2movelst, level);
            qsort(b2movelst, b2, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
          }
          x =  - NegaScout(0, level+1, &line, b2movelst, b2, NextDepth, -beta, -alpha /*-beta+1*/, NextColor, &iretNull, IsPVnode, 0, NULL,0);
          if (iretNull>=0) {
            NullBest.u = b2movelst[iretNull].u;
          }
        }
        if (x>=beta) {
          *bestMoveIndex = TERMINAL_NODE;
          return x;
        }
      }
    }
    /* late move generation */
    if ( n==0 ) {
      if (color==black) {
        n=FindAllBlackMoves(mlst, level-1);
      } else {
        n=FindAllWhiteMoves(mlst, level-1);
      }
      /* Adjust move priorities */
      if (FollowingPV && GlobalPV.cmove>level-1) {
        GPVmp = &GlobalPV.argmove[level-1];
      } else {
        GPVmp = NULL;
      }
      for (i=0; i<n; i++) {
        if (GPVmp && mlst[i].m.from==GPVmp->m.from && mlst[i].m.to==GPVmp->m.to) {
          mlst[i].m.mvv_lva = 127; /* Move follows PV*/
          ShouldIID = 0;
        } else if (mlst[i].m.from==HashBest.m.from && mlst[i].m.to==HashBest.m.to) {
          mlst[i].m.mvv_lva = 126; /* Move from Hash table */
          ShouldIID = 0;
        } else if (ThreatP && mlst[i].m.from==ThreatP->m.from && mlst[i].m.to==ThreatP->m.to)
          mlst[i].m.mvv_lva = 110; /* Move found as threat from previous level Null Move search */
      }
      /* Sort generated moves using native C quick-sort algorithm */
      qsort(mlst, n, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
    }
    if (level>1) {
     if (ShouldIID && !BeingInCheck && depth>IID_DEPTH) { /* Internal Iterative Deepening */
      x = 0;
      legality_checked=1;
      for (i=0; i<n; i++) {
        TryMove(&mlst[i]);
        if (color==black) {
          if (BlackKingInCheck()) {
            mlst[i].m.flag=0;
            RetractLastMove();
            continue;
          }
        } else {
          if (WhiteKingInCheck()) {
            mlst[i].m.flag=0;
            RetractLastMove();
            continue;
          }
        }
        x++;
        RetractLastMove();
      }
      if (x==0) {
        if (BeingInCheck) {
          a = -INFINITY_ + (mv_stack_p - Starting_Mv);
        } else {
          a = 0;
        }
        *bestMoveIndex = TERMINAL_NODE;
        return a;
      }
      IID_d = depth / 3 ;
      Internal_Iterative_Deepening(mlst, n, NextColor,IID_d, alpha, beta);
     }
    } else { /*level==1*/
      legality_checked=1;
    }

    a = alpha;
    for (i=0; i<n; i++) {
      /* foreach child of node */
      if (CheckTime()) {
        TimeIsUp = 1;
      }
      if (legality_checked==1) {
        if (mlst[i].m.flag==0) {
          continue;
        } else {
          PushStatus();
          MakeMove(&mlst[i]);
        }
      } else {
        PushStatus();
        MakeMove(&mlst[i]);
        if (color==black) {
          if (BlackKingInCheck()) {
            RetractLastMove();
            PopStatus();
            continue;
          }
        } else {
          if (WhiteKingInCheck()) {
            RetractLastMove();
            PopStatus();
            continue;
          }
        }
      }
      Tbest.u = 0;
      if (CheckForDraw()) {
        t = 0;
      } else if (color==black) {
        /* if our move just played gives check, generate evasions and do not reduce depth so we can search deeper */
        nChecks = WhiteKingInCheckInfo(CheckAttacks, &nCheckPieces);
        if (nChecks) { /* early move generation */
          CanReduct=0;
          NextDepth = depth;
          w2=FindAllWhiteEvasions(w2movelst, CheckAttacks, nChecks, nCheckPieces);
          qsort(w2movelst, w2, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
        } else {
          NextDepth = depth-1;
          CanReduct = (IsMaterialEnough > 7) && (!IsPVnode) && (!BeingInCheck) && 
                      ((int)mlst[i].m.mvv_lva < TACTICAL_MARGIN);
          if ( CanReduct ) {
            if ( FutilityPruning(NextDepth, e, a) ) {
              RetractLastMove();
              PopStatus();
              continue;
            }
          }
          w2=0;
        }
        CurrMoveFollowsPV=0;
        if (FollowingPV) {
          if (GlobalPV.cmove>level-1) {
            if (mlst[i].m.from==GlobalPV.argmove[level-1].m.from  &&  mlst[i].m.to==GlobalPV.argmove[level-1].m.to ) {
              CurrMoveFollowsPV=1;
            }
          }
        }
        if (ngmoves==0) { /* First move to search- full window [-beta,-alpha] used */
          t =  - NegaScout(1, level+1, &line, w2movelst, w2, NextDepth, -beta, -a, NextColor, &iret, PV_NODE, nChecks, &NullBest,CurrMoveFollowsPV);
        } else {
          if (CanReduct && (ngmoves >= LMR_MOVES) && (depth > LMR_DEPTH_LIMIT)) {
            /* LMR - Search with reduced depth and scout window [-alpha-1,-alpha] */
            t =  - NegaScout(1, level+1, &line, w2movelst, w2, depth-2, -a-1, -a, NextColor, &iret, CUT_NODE, nChecks, &NullBest,CurrMoveFollowsPV);
          } else t = a+1;  /* Ensure that re-search is done. */

          if (t > a) {
            /* Search using normal depth and scout window [-alpha-1,-alpha] */
            t =  - NegaScout(1, level+1, &line, w2movelst, w2, NextDepth, -a-1, -a, NextColor, &iret, CUT_NODE, nChecks, &NullBest,CurrMoveFollowsPV); 
            if ( (t > a) && (t < beta) ) {
              /* re-search using full window */
              t = - NegaScout(1, level+1, &line, w2movelst, w2, NextDepth, -beta, -a, NextColor, &iret, PV_NODE, nChecks, &NullBest,CurrMoveFollowsPV);
            }
          }
        }
        if (iret>=0) { /* Update Best defense for later use in PV line update */
          Tbest.u = w2movelst[iret].u;
          if (level==1 && mlst[i].u==GlobalPV.argmove[0].u && depth>START_DEPTH+1) {
            if (t < (ngmax - PV_CHANGE_THRESH) ) {
              danger=1;
              OutputDanger(depth, t, &Tbest);
            }
          }
        } 
      } else { /* color==white */
        /* if our move just played gives check do not reduce depth so we can search deeper */
        nChecks = BlackKingInCheckInfo(CheckAttacks, &nCheckPieces);
        if (nChecks) { /* early move generation */
          CanReduct=0;
          NextDepth = depth;
          b2=FindAllBlackEvasions(b2movelst, CheckAttacks, nChecks, nCheckPieces);
          qsort(b2movelst, b2, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
        } else {
          NextDepth = depth-1;
          CanReduct = (IsMaterialEnough > 7) && (!IsPVnode) && (!BeingInCheck) && 
                      ((int)mlst[i].m.mvv_lva < TACTICAL_MARGIN);
          if ( CanReduct ) { /* Futility pruning */
            if ( FutilityPruning(NextDepth, e, a) ) {
              RetractLastMove();
              PopStatus();
              continue;
            }
          }
          b2=0;
        }
        CurrMoveFollowsPV=0;
        if (FollowingPV) {
          if (GlobalPV.cmove>level-1) {
            if (mlst[i].m.from==GlobalPV.argmove[level-1].m.from  && mlst[i].m.to==GlobalPV.argmove[level-1].m.to ) {
              CurrMoveFollowsPV=1;
            }
          }
        }
        if (ngmoves==0) { /* First move to search- full window [-beta,-alpha] used */
          t =  - NegaScout(1, level+1, &line, b2movelst, b2, NextDepth, -beta, -a, NextColor, &iret, PV_NODE, nChecks, &NullBest,CurrMoveFollowsPV);
        } else {
          if (CanReduct && (ngmoves >= LMR_MOVES) && (depth > LMR_DEPTH_LIMIT)) {
            /* LMR - Search with reduced depth and scout window [-alpha-1,-alpha] */
            t =  - NegaScout(1, level+1, &line, b2movelst, b2, depth-2, -a-1, -a, NextColor, &iret, CUT_NODE, nChecks, &NullBest,CurrMoveFollowsPV);
          } else t = a+1;  /* Ensure that re-search is done. */

          if (t > a) {
            /* Search normal depth and scout window [-alpha-1,-alpha] */
            t =  - NegaScout(1, level+1, &line, b2movelst, b2, NextDepth, -a-1, -a, NextColor, &iret, CUT_NODE, nChecks, &NullBest,CurrMoveFollowsPV); 
            if ( (t > a) && (t < beta) ) {
              /* re-search using full window */
              t = - NegaScout(1, level+1, &line, b2movelst, b2, NextDepth, -beta, -a, NextColor, &iret, PV_NODE, nChecks, &NullBest,CurrMoveFollowsPV);
            }
          }
        }
        if (iret>=0) { /* Update Best defense for later use in PV line update */
          Tbest.u = b2movelst[iret].u;
          if (level==1 && mlst[i].u==GlobalPV.argmove[0].u && depth>START_DEPTH+1) {
            if (t < (ngmax - PV_CHANGE_THRESH) ) {
              danger=1;
              OutputDanger(depth, t, &Tbest);
            }
          }
        }
      }
      LastMoveToSquare  = mlst[i].m.to;
      LastMovePieceType = board[LastMoveToSquare]->type;
      RetractLastMove();
      PopStatus();
      if (TimeIsUp) {
        if (!danger)
          return a;
      }
      /*the following constitutes alpha-beta pruning*/
      if (t>a) {
        a = t;
        *bestMoveIndex = i;
        /* Update Principal Variation */
        if (Tbest.u) {
          pline->argmove[0].u = Tbest.u;
          memcpy(pline->argmove + 1, line.argmove, line.cmove * sizeof(MOVE));
          pline->cmove = line.cmove + 1;
        } else {
          pline->cmove = 0;
        }
        if (a>=beta) { /*-- cut-off --*/
          /* Update depth killers for non captures */
          if (board[LastMoveToSquare]->type == 0) {
            if (color==black) {
              B_Killers[1][level-1] = B_Killers[0][level-1];
              B_Killers[0][level-1] = mlst[i].u;
            } else {
              W_Killers[1][level-1] = W_Killers[0][level-1];
              W_Killers[0][level-1] = mlst[i].u;
            }
          }
          /* Update Transposition table */
          if (level&1) {
            Update_TT(T_T, depth, a, CHECK_BETA, move_stack[mv_stack_p].PositionHash, mlst[i]);
          } else {
            Update_TT(Opp_T_T, depth, a, CHECK_BETA, move_stack[mv_stack_p].PositionHash, mlst[i]);
          }
          return a;
        }
        /* Update history values for non captures */
        if (board[LastMoveToSquare]->type == 0) {
          /* Non capture move increased alpha - increase (piece,square) history value */
          if (color==black) {
            if (B_history[LastMovePieceType - BPAWN][LastMoveToSquare]==0) {
              B_history[LastMovePieceType - BPAWN][LastMoveToSquare] = -MAX_DEPTH;
            }
            B_history[LastMovePieceType - BPAWN][LastMoveToSquare] += depth;
            if (B_history[LastMovePieceType - BPAWN][LastMoveToSquare] >=0 )
              B_history[LastMovePieceType - BPAWN][LastMoveToSquare] = -1;
          } else {
            if (W_history[LastMovePieceType - WPAWN][LastMoveToSquare]==0) {
              W_history[LastMovePieceType - WPAWN][LastMoveToSquare] = -MAX_DEPTH;
            }
            W_history[LastMovePieceType - WPAWN][LastMoveToSquare] += depth;
            if (W_history[LastMovePieceType - WPAWN][LastMoveToSquare] >=0 )
              W_history[LastMovePieceType - WPAWN][LastMoveToSquare] = -1;
          }
        }
      }
      ngmoves++;
    }/* for each node */
    if (ngmoves==0) {
      if (BeingInCheck) {/* Mate */
        a = -INFINITY_ + (mv_stack_p - Starting_Mv);
      } else {/* StaleMate */
        a = 0;
      }
      *bestMoveIndex = TERMINAL_NODE;
    }
    /* Update Transposition table */
    if (a > alpha) {
      MOVE smove;
      if ( (*bestMoveIndex) != TERMINAL_NODE ) {
        smove = mlst[*bestMoveIndex];
      } else {
        smove.u=0;
      }
      if (level&1) {
        Update_TT(T_T, depth, a, EXACT, move_stack[mv_stack_p].PositionHash, smove);
      } else {
        Update_TT(Opp_T_T, depth, a, EXACT, move_stack[mv_stack_p].PositionHash, smove);
      }
    } else {
      MOVE smove;
      smove.u=0;
      if (level&1) {
        Update_TT(T_T, depth, a, CHECK_ALPHA, move_stack[mv_stack_p].PositionHash, smove);
      } else {
        Update_TT(Opp_T_T, depth, a, CHECK_ALPHA, move_stack[mv_stack_p].PositionHash, smove);
      }
    }
    return a;
  }
}

int PlayAndSortMoves(MOVE q[], int n, int Nextcolor, int depth, int endL)
{
  register int i, j, maxscore=-INFINITY_-1, maxi, utemp;
  int sortV[MAXMV];
  for (i=0; i<n; i++) {
    if ((int)q[i].m.flag == 0) {
      sortV[i] = -INFINITY_;
    } else {
      PushStatus();
      MakeMove(&q[i]);
      sortV[i]  = - Negalight(depth-1, -INFINITY_, INFINITY_, Nextcolor);
      RetractLastMove();
      PopStatus();
    } 
  }
  /* sort q[] using sortV */
  for (j=0;j<endL;j++) {
    maxscore = -INFINITY_-1;
    maxi = -1;
    for (i=j; i<n; i++) {
      if (sortV[i] > maxscore) {
        maxscore = sortV[i];
        maxi = i;
      }
    }
    if (maxi>=0) {
      utemp = q[maxi].u;
      q[maxi].u = q[j].u;
      q[j].u = utemp;
      utemp = sortV[maxi];
      sortV[maxi] = sortV[j];
      sortV[j] = utemp;
    }
  }
  return sortV[0];
}

void PrintMoveOutput(int depth, int Goodmove)
{
  if (Xoutput==_XBOARD_OUTPUT) {
    printf("%d %d %d %d ", depth, ngmax, (GetMillisecs() - start_time) / 10, nodes);
    PrintfPVline(&GlobalPV,Goodmove);
    fflush(stdout);
  } else if (Xoutput==_NORMAL_OUTPUT) {
    printf("%3d%7.2lf%7.2lf   ",depth, 0.01*ngmax, SECONDS_PASSED);
    PrintfPVline(&GlobalPV,Goodmove);
  } 
}

unsigned long long Perft(int depth, int color, int level, int UseHash)
{
  MOVE move_list[MAXMV];
  register int i, n_moves, actual;
  unsigned long long nodes = 0;
  if (depth==0) 
    return 1;
  if (UseHash && level>1) {
    register unsigned int Indx = move_stack[mv_stack_p].PositionHash & MAX_TT;
    unsigned int key32 = move_stack[mv_stack_p].PositionHash >> 32;
    if (level&1) {
      if (T_T[Indx].PositionHashUpper == key32) {
       if (T_T[Indx].depth == depth) {
        return (T_T[Indx].value);
       }
      }
    } else {
      if (Opp_T_T[Indx].PositionHashUpper == key32) {
       if (Opp_T_T[Indx].depth == depth) {
        return (Opp_T_T[Indx].value);
       }
      }
    }
  }
  if (color==white) {
    n_moves=FindAllWhiteMoves(move_list);
    for (i = 0; i < n_moves; i++) {
      PushStatus();
      MakeMove(&move_list[i]);
      if (WhiteKingInCheck()) {
        RetractLastMove();
        PopStatus();
        continue;
      }
      nodes += Perft(depth-1, black, level+1, UseHash);
      RetractLastMove();
      PopStatus();
    }
  } else {
    n_moves=FindAllBlackMoves(move_list);
    for (i = 0; i < n_moves; i++) {
      PushStatus();
      MakeMove(&move_list[i]);
      if (BlackKingInCheck()) {
        RetractLastMove();
        PopStatus();
        continue;
      }
      nodes += Perft(depth-1, white, level+1, UseHash);
      RetractLastMove();
      PopStatus();
    }
  }
  if (UseHash) {
    register unsigned int Indx = move_stack[mv_stack_p].PositionHash & MAX_TT;
    unsigned int key32 = move_stack[mv_stack_p].PositionHash >> 32;
    if (level&1) {
      T_T[Indx].value = nodes;
      T_T[Indx].depth = depth;
      T_T[Indx].PositionHashUpper = key32;
    } else {
      Opp_T_T[Indx].value = nodes;
      Opp_T_T[Indx].depth = depth;
      Opp_T_T[Indx].PositionHashUpper = key32;
    }
  }
  return nodes;
}

int GetWhiteBestMove(MOVE *mP)
{
  int ret=0, d, w_moves, e, IsMaterialEnough, actual, unique, i;
  int tempNG, sortMax, Alpha, Beta, InCheck;
  MOVE wmovelst[MAXMV], Threat;
  LINE line;
  InitTime();
  nodes = 0;
  Starting_Mv=mv_stack_p;
  w_moves=FindAllWhiteMoves(wmovelst);
  actual=0;
  for (i=0; i<w_moves; i++) {
    PushStatus();
    MakeMove(&wmovelst[i]);
    if (WhiteKingInCheck()) {
      RetractLastMove();
      PopStatus();
      wmovelst[i].m.flag=0;
      wmovelst[i].m.mvv_lva= -126;
      continue;
    }
    RetractLastMove();
    PopStatus();
    unique=i;
    actual++;
  }
  if (actual>1)
    qsort(wmovelst, w_moves, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
  if (actual==0) {
    if (WhiteKingInCheck()) {
      if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("Black Mates.  GAME OVER  (0 - 1)");
      } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("0-1 {Black Mates}\n");
      }
    } else {
      if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("Drawn. Stalemate.  GAME OVER  (1/2 - 1/2)");
      } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("1/2-1/2 {Draw. Stalemate.}\n");
      }
    }
    return 0;
  }
  if (IsBookLine(&ret,wmovelst,w_moves, white)) {
    mP->u = wmovelst[ret].u;
    return 1;
  } else {
    e = StaticEval(&IsMaterialEnough);

    if (IsMaterialEnough==0) {
      if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("Drawn. Not enought pieces for mate.  GAME OVER  (1/2 - 1/2)");
      } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("1/2-1/2 {Draw. Not enough material.}\n");
        return 0;
      }
    }
    ret=0;
    if (actual==1) {
      mP->u = wmovelst[unique].u;
      return 1;
    } else {
     InCheck = WhiteKingInCheck();
     if (InCheck) {
       Threat.u = 0;
     } else { /*-- First Try to find threat for opponent --*/
       int key=-1, actual_oppn;
       MOVE thrlst[MAXMV];
       int oppn = FindAllBlackMoves(thrlst);
       actual_oppn=0;
       for (i=0; i<oppn; i++) {
         PushStatus();
         MakeMove(&thrlst[i]);
         if (BlackKingInCheck()) {
           thrlst[i].m.flag=0;
           thrlst[i].m.mvv_lva= -126;
           RetractLastMove();
           PopStatus();
           continue;
         }
         RetractLastMove();
         PopStatus();
         actual_oppn++;
       }
       qsort(thrlst, oppn, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
       if (actual_oppn>THREAT_THRESH) {
         /* Find threat using a shallow negamax search */
         if (PlayAndSortMoves(thrlst, oppn, white/*--next color is ours--*/, THREAT_DEPTH, 1/*1 move needed*/)) {
           Threat.u = thrlst[0].u;
           if (Xoutput==_NORMAL_OUTPUT)
             printf("\n Black's Threat is %s (found in %7.2lf seconds)\n",  TranslateMoves(&Threat), SECONDS_PASSED);
         } else {
           Threat.u = 0;
         }
       }
     }
     /*-- Then Sort Our starting move list using a very shallow negamax search --*/
     sortMax=PlayAndSortMoves(wmovelst, w_moves, black, THREAT_DEPTH+1, w_moves);
     if (Xoutput==_NORMAL_OUTPUT) {
       printf("\nInitial Eval:%d\n",sortMax);
       printf("\nDepth Eval  Seconds Principal Variation  \n ---  ----  ------- -------------------\n");
     }
     TimeIsUp = 0;

     /* If opponent answered following previous PV, add the computer reply choice first in the moves list*/
     if (PlayerMove.u!=0 && 
         GlobalPV.argmove[1].m.flag==PlayerMove.m.flag  &&
         GlobalPV.argmove[1].m.from==PlayerMove.m.from  &&
         GlobalPV.argmove[1].m.to==PlayerMove.m.to        
         ) 
     {
       FindAndUpdateInPlace(wmovelst, w_moves, GlobalPV.argmove[2],0);
       if (Xoutput==_NORMAL_OUTPUT)
         printf("Previous PV followed\n");
     }
     for (d=START_DEPTH; d<=MAX_DEPTH; d++) { /* Iterative deepening method*/ 
      danger = 0;
      /* If depth sufficient, then put previous PV[0] first in move list */
      if (d>START_DEPTH) {
        FindAndUpdateInPlace(wmovelst, w_moves, GlobalPV.argmove[0],0);
      } 
      Alpha = -INFINITY_;
      Beta  =  INFINITY_;
      tempNG = NegaScout(0, 1, &line, wmovelst, w_moves,  d, Alpha, Beta, white, &ret, PV_NODE, InCheck, &Threat, 1);
      if (TimeIsUp) {
        if (!danger)
          break;
      }
      if (ret>=0) {
        int exclamation=0;
        ngmax = tempNG;
        GlobalPV.argmove[0].u = wmovelst[ret].u;
        memcpy(GlobalPV.argmove + 1, line.argmove, line.cmove * sizeof(MOVE));
        GlobalPV.cmove  = line.cmove + 1;
        exclamation = (d>START_DEPTH) && ((tempNG-sortMax) > PV_CHANGE_THRESH);
        PrintMoveOutput(d, exclamation);
      }
      if ( (ngmax > MATE_CUTOFF || ngmax < -MATE_CUTOFF) && (d>FUTIL_DEPTH) )
        break;
      PrevNgmax=ngmax;
     }
     if ( ngmax < -RESIGN_EVAL ) {
       if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("White resigns.  GAME OVER  (0 - 1)");
       } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("0-1 {White resigns}\n");
        return 0;
       }
     }
    }
  } 
  mP->u = GlobalPV.argmove[0].u;
  return 1;
}

int GetBlackBestMove(MOVE *mP)
{
  int ret=0, d, black_moves, e, IsMaterialEnough, actual, unique, i;
  int tempNG, sortMax, Alpha, Beta, InCheck;
  MOVE bmovelst[MAXMV], Threat;
  LINE line;
  InitTime();
  Starting_Mv=mv_stack_p;
  nodes = 0;
  black_moves=FindAllBlackMoves(bmovelst);
  actual=0;
  for (i=0; i<black_moves; i++) {
    PushStatus();
    MakeMove(&bmovelst[i]);
    if (BlackKingInCheck()) {
      RetractLastMove();
      PopStatus();
      bmovelst[i].m.flag=0;
      bmovelst[i].m.mvv_lva= -126;
      continue;
    }
    RetractLastMove();
    PopStatus();
    unique=i;
    actual++;
  }
  if (actual>1)
    qsort(bmovelst, black_moves, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
  if (actual==0) {
    if (BlackKingInCheck()) {
      if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("White Mates.  GAME OVER  (1 - 0)");
      } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("1-0 {White Mates}\n");
        return 0;
      }
    } else {
      if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("Drawn. Stalemate.  GAME OVER  (1/2 - 1/2)");
      } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("1/2-1/2 {Draw. Stalemate.}\n");
        return 0;
      }
    } 
  }
  if (IsBookLine(&ret,bmovelst,black_moves, black)) {
    mP->u = bmovelst[ret].u;
    return 1;
  } else {
    e = StaticEval(&IsMaterialEnough);

    if (IsMaterialEnough==0) {
      if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("Drawn. Not enought pieces for mate.  GAME OVER  (1/2 - 1/2)");
      } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("1/2-1/2 {Draw. Not enough material.}\n");
        return 0;
      }
    }
    ret=0;
    if (actual==1) {
      mP->u = bmovelst[unique].u;
      return 1;
    } else {
     InCheck = BlackKingInCheck();
     if (InCheck) {
       Threat.u = 0;
     } else { /*-- First Try to find threat for opponent --*/
       int key=-1, actual_oppn;
       MOVE thrlst[MAXMV];
       int oppn = FindAllWhiteMoves(thrlst);
       actual_oppn=0;
       for (i=0; i<oppn; i++) {
         PushStatus();
         MakeMove(&thrlst[i]);
         if (WhiteKingInCheck()) {
           RetractLastMove();
           PopStatus();
           thrlst[i].m.flag=0;
           thrlst[i].m.mvv_lva= -126;
           continue;
         }
         RetractLastMove();
         PopStatus();
         actual_oppn++;
       }
       qsort(thrlst, oppn, sizeof(MOVE), MOVE_cmp_by_mvv_lva);
       if (actual_oppn>THREAT_THRESH) {
         if (PlayAndSortMoves(thrlst, oppn, black/*next color*/, THREAT_DEPTH, 1/*we need only threat move*/)) {
           Threat.u = thrlst[0].u;
           if (Xoutput==_NORMAL_OUTPUT)
             printf("\n White's Threat is %s (found in %7.2lf seconds)\n",  TranslateMoves(&Threat), SECONDS_PASSED);
         } else {
           Threat.u = 0;
         }
       }
     }
     /*-- Then Sort Our starting moves using a very shallow negamax search --*/
     sortMax = PlayAndSortMoves(bmovelst, black_moves, white, THREAT_DEPTH+1, black_moves);
     if (Xoutput==_NORMAL_OUTPUT) {
       printf("\nInitial Eval:%d\n",sortMax);
       printf("\nDepth Eval  Seconds Principal Variation  \n ---  ----  ------- -------------------\n");
     }
     TimeIsUp = 0;
     /* If opponent answered following previous PV add the computer reply choice first in the moves list */
     if (PlayerMove.u!=0 &&
         GlobalPV.argmove[1].m.flag==PlayerMove.m.flag  &&
         GlobalPV.argmove[1].m.from==PlayerMove.m.from  &&
         GlobalPV.argmove[1].m.to==PlayerMove.m.to        
         ) 
     {
       FindAndUpdateInPlace(bmovelst, black_moves, GlobalPV.argmove[2],0);
       if (Xoutput==_NORMAL_OUTPUT)
         printf("Previous PV followed\n");
     }
     for (d=START_DEPTH; d<=MAX_DEPTH; d++) { /* Iterative deepening method */
      danger = 0;
      /* If depth sufficient then put previous PV[0] first in move list */
      if (d>START_DEPTH) {
        FindAndUpdateInPlace(bmovelst, black_moves, GlobalPV.argmove[0],0);
      } 
      Alpha = -INFINITY_;
      Beta  =  INFINITY_;
      tempNG = NegaScout(0, 1, &line, bmovelst, black_moves,  d, Alpha, Beta, black, &ret, PV_NODE, InCheck, &Threat, 1);
      if (TimeIsUp) {
        if (!danger)
          break;
      }
      if (ret>=0) {
        int exclamation=0;
        ngmax = tempNG;
        GlobalPV.argmove[0].u = bmovelst[ret].u;
        memcpy(GlobalPV.argmove + 1, line.argmove, line.cmove * sizeof(MOVE));
        GlobalPV.cmove  = line.cmove + 1;
        exclamation  = (d>START_DEPTH) && ((tempNG-sortMax) > PV_CHANGE_THRESH);
        PrintMoveOutput(d, exclamation);
      }
      if ( (ngmax > MATE_CUTOFF || ngmax < -MATE_CUTOFF) && (d>FUTIL_DEPTH) )
        break;
      PrevNgmax=ngmax;
     }
     if ( ngmax < -RESIGN_EVAL ) {
       if (Xoutput==_NORMAL_OUTPUT) {
        ExitErrorMesg("Black resigns.  GAME OVER  (1 - 0)");
       } else if (Xoutput==_XBOARD_OUTPUT) {
        printf("1-0 {Black resigns}\n");
        return 0;
       }
     }
    } 
  } 
  mP->u = GlobalPV.argmove[0].u;
  return 1;
}

/* ------------------- GAME CONSOLE/XBOARD ----------------------------------- */

int GetPlayerMove(int *xy1, int *xy2, int *flag)
{
  char buf[60];
  int x1,y1,x2,y2;
  int prompted=0;
  for (;;) {
    if (!prompted) {
      printf("\nGive move (q=quit) : ");
      prompted=1;
    }
    gets(buf);
    if (!strcmp(buf,"retract") || buf[0]=='r') {
      return 2;
    }
    if (!strcmp(buf,"go")) {
      return 4;
    }
    if (!strcmp(buf,"bye") || !strcmp(buf,"resign") || buf[0]=='q') {
      ExitErrorMesg("Thank you for playing!");
    }
    if (buf[0]>='a' && buf[0]<='h') {
      x1 = buf[0] - 'a';
      if (buf[1]>='1' && buf[1]<='8') {
        y1 = buf[1] - '1';
        if (buf[2]>='a' && buf[2]<='h') {
          x2 = buf[2] - 'a';
          if (buf[3]>='1' && buf[3]<='8') {
            y2 = buf[3] - '1';
            break;
          }
        }
      }
    }
  }
  *xy1 = 10*y1+x1+21;
  *xy2 = 10*y2+x2+21;
  if (board[*xy1]->type==WPAWN) {
    if (*xy2>=A8) {
      switch(buf[4]) {
        case 'r': *flag=WROOK; break;
        case 'n': *flag=WKNIGHT; break;
        case 'b': *flag=WBISHOP; break;
        case 'q': *flag=WQUEEN; break;
        default: fprintf(stderr,"Give promotion piece number(knight=1,bishop=2,rook=3,queen=4), :");
                 scanf("%d",flag);
                 *flag = (*flag) + 2;
                 break;
      }
    } else *flag=WPAWN;
  } else if (board[*xy1]->type==BPAWN) {
    if (*xy2<=H1) {
      switch(buf[4]) {
        case 'r': *flag=BROOK; break;
        case 'n': *flag=BKNIGHT; break;
        case 'b': *flag=BBISHOP; break;
        case 'q': *flag=BQUEEN; break;
        default: fprintf(stderr,"Give promotion piece number(knight=1,bishop=2,rook=3,queen=4), :");
                 scanf("%d",flag);
                 *flag = (*flag) + 2;
                 *flag = black + (*flag);
                 break;
      }
    } else *flag=BPAWN;
  } else {
    *flag=1;
  }
  return 0;
}

void UpdateSpecialConditions(MOVE  *amovep)
{
  register int i, bl_pieces=0, wh_pieces=0;
  FiftyMoves++;
  if ((board[amovep->m.from]->type == WPAWN) || (board[amovep->m.from]->type == BPAWN)) 
  { /* pawn move */
    FiftyMoves = 0;
  }
  if (board[amovep->m.to]->type > 0) 
  { /* capture */
    FiftyMoves = 0;
  }
  for (i=0; i<16; i++) {
    if (Bpieces[i].xy>0) {
      bl_pieces++;
    } 
    if (Wpieces[i].xy>0) {
      wh_pieces++;
    }
  }
  if (bl_pieces==1 && Edge[bking]) {
    LoneKingReachedEdge = 1;
  }
  if (wh_pieces==1 && Edge[wking]) {
    LoneKingReachedEdge = 1;
  }
  ResetHistory();
}

void Play(void)
{
 int i, wn, bn, from, to, fl, actual;
 MOVE amove, wmoves[MAXMV], bmoves[MAXMV];
 int e, IsMaterialEnough;
 for (;;) {
PlayWhite:
  side=white;
  e = StaticEval(&IsMaterialEnough);
  if (IsMaterialEnough==0) {
    ExitErrorMesg("Draw.  Not enough Material. (1/2 - 1/2)");
  }  
  /* Check if white is checkmated */
  wn=FindAllWhiteMoves(wmoves);
  actual=0;
  for (i=0; i<wn; i++) {
    TryMove(&wmoves[i]);
    if (WhiteKingInCheck()) {
      wmoves[i].m.flag=0;
      RetractLastMove();
      continue;
    }
    RetractLastMove();
    actual++;
  }
  if (actual==0) {
    ShowBoard();
    if (WhiteKingInCheck()) {
      ExitErrorMesg("Black Checkmates !!  GAME OVER (0-1)");
    } else {
      ExitErrorMesg("Stalemate.  GAME OVER  (1/2 - 1/2)");
    }
  }  
  if ( ComputerSide == white) {
    printf("\n Board before Computer starts thinking ");
    ShowBoard();
    if (!GetWhiteBestMove(&amove))
      continue;
    UpdateSpecialConditions(&amove);
    printf("\n Computer decided to play: %s in %7.2lf secs",TranslateMoves(&amove), SECONDS_PASSED);
  } else {
    int comm;
    do {
      ShowBoard();
      comm = GetPlayerMove(&from, &to, &fl);
      if (comm==2) {
        RetractLastMove();
        PopStatus();
        RetractLastMove();
        PopStatus();
        ShowBoard();
        while (GetPlayerMove(&from, &to, &fl)>0);
      }
      if (comm==4) {
        if (ComputerSide==none) {
          fprintf(stderr,"Give Computer Time (seconds per move) : ");
          scanf("%d", &max_time);
          max_time *= 1000;
        }
        ComputerSide = white;
        goto PlayWhite;
      }
      amove.m.flag = fl;
      amove.m.from = from;
      amove.m.to = to;
      amove.m.mvv_lva=0;
    } while (!MoveIsValid(amove, wmoves, wn));
    PlayerMove.u = amove.u;
    UpdateSpecialConditions(&amove);
  }
  PushStatus();
  MakeMove(&amove);
  AddMoveToLine(amove.m.from,amove.m.to);
  #ifdef DBGMATERIAL
  fprintf(stderr,"\nMaterial=%lf\n",move_stack[mv_stack_p].material/100.0);
  #endif
  if (HashRepetitions() == 3) {
    ShowBoard();
    ExitErrorMesg("1/2-1/2 {Draw by repetition}\n");
  }
  if (FiftyMoves>=100) {
    ShowBoard();
    ExitErrorMesg("1/2-1/2 {Draw by fifty moves rule}\n");
  }
PlayBlack:
  side=black;
  e = StaticEval(&IsMaterialEnough);
  if (IsMaterialEnough==0) {
    ExitErrorMesg("Draw.  Not enough Material. (1/2 - 1/2)");
  }  
  /* Check if black is checkmated */
  bn=FindAllBlackMoves(bmoves);
  actual=0;
  for (i=0; i<bn; i++) {
    TryMove(&bmoves[i]);
    if (BlackKingInCheck()) {
      bmoves[i].m.flag=0;
      RetractLastMove();
      continue;
    }
    RetractLastMove();
    actual++;
  }
  if (actual==0) {
    if (BlackKingInCheck()) {
      ShowBoard();
      ExitErrorMesg("White Checkmates !!  GAME OVER (1-0)");
    } else {
      ShowBoard();
      ExitErrorMesg("Stalemate.  GAME OVER  (1/2 - 1/2)");
    }
  }
  if (ComputerSide == black) {
    printf("\n Board before Computer starts thinking ");
    ShowBoard();
    if (!GetBlackBestMove(&amove))
      continue;
    UpdateSpecialConditions(&amove);
    printf("\n Computer decided to play : %s in %7.2lf secs",TranslateMoves(&amove), SECONDS_PASSED);
  } else {
    int comm;
    do {
      ShowBoard();
      comm = GetPlayerMove(&from, &to,&fl);
      if (comm==2) {
        RetractLastMove();
        PopStatus();
        RetractLastMove();
        PopStatus();
        ShowBoard();
        while (GetPlayerMove(&from, &to, &fl)>0);
      }
      if (comm==4) {
        if (ComputerSide==none) {
          fprintf(stderr,"Give Computer Time (seconds per move) : ");
          scanf("%d", &max_time);
          max_time *= 1000;
        }
        ComputerSide = black;
        goto PlayBlack;
      }
      amove.m.flag = fl;
      amove.m.from = from;
      amove.m.to = to;
      amove.m.mvv_lva=0;
    } while (!MoveIsValid(amove, bmoves, bn));
    PlayerMove.u = amove.u;
    UpdateSpecialConditions(&amove);
  }
  PushStatus();
  MakeMove(&amove);
  AddMoveToLine(amove.m.from,amove.m.to);
  #ifdef DBGMATERIAL
  fprintf(stderr,"\nMaterial=%lf\n",move_stack[mv_stack_p].material/100.0);
  #endif
  if (HashRepetitions() == 3) {
    ShowBoard();
    ExitErrorMesg("1/2-1/2 {Draw by repetition}\n");
  }
  if (FiftyMoves>=100) {
    ShowBoard();
    ExitErrorMesg("1/2-1/2 {Draw by fifty moves rule}\n");
  }
 }
}

void ReadXboardPosition(void)
{
  char cbuf[256], command[256];
  int i, Xcolor=0;
  while (fgets(cbuf, 256, stdin) != NULL) {
    if (cbuf[0] == '\n')
      break;
    sscanf(cbuf, "%s", command);
    if (!strcmp(command, "#")) {
      EmptyBoard();
    }
    if (!strcmp(command, "c")) {
      Xcolor=black; 
    }
    if (!strcmp(command, ".")) {
      break; 
    }
    if (cbuf[0] && cbuf[1] && cbuf[2]) {
      switch (cbuf[0]) {
        case '\n':
        case '\t':
        case ',':
        case ' ': 
          break;
        case 'K': 
          if (Xcolor==black) {
            bking = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            Bpieces[0].xy = bking;
            board[bking] = &Bpieces[0];
          } else {
            wking = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            Wpieces[0].xy = wking;
            board[wking] = &Wpieces[0];
          }
          break;
        case 'Q': 
          if (Xcolor==black) {
            if (Bpieces[1].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[1];
              Bpieces[1].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Bpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[i];
                  Bpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Bpieces[i].type = BQUEEN;
                  break;
                } 
              }
            }
          } else {
            if (Wpieces[1].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[1];
              Wpieces[1].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Wpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[i];
                  Wpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Wpieces[i].type = WQUEEN;
                  break;
                } 
              }
            }
          }
          break;
        case 'R': 
          if (Xcolor==black) {
            if (Bpieces[2].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[2];
              Bpieces[2].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else if (Bpieces[3].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[3];
              Bpieces[3].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Bpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[i];
                  Bpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Bpieces[i].type = BROOK;
                  break;
                }
              }
            } 
          } else {
            if (Wpieces[2].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[2];
              Wpieces[2].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else if (Wpieces[3].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[3];
              Wpieces[3].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Wpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[i];
                  Wpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Wpieces[i].type = WROOK;
                  break;
                }
              }
            } 
          }
          break;
        case 'B': 
          if (Xcolor==black) {
            if (Bpieces[4].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[4];
              Bpieces[4].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else if (Bpieces[5].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[5];
              Bpieces[5].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Bpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[i];
                  Bpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Bpieces[i].type = BBISHOP;
                  break;
                }
              }
            } 
          } else {
            if (Wpieces[4].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[4];
              Wpieces[4].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else if (Wpieces[5].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[5];
              Wpieces[5].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Wpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[i];
                  Wpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Wpieces[i].type = WBISHOP;
                  break;
                } 
              }
            } 
          }
          break;
        case 'N': 
          if (Xcolor==black) {
            if (Bpieces[6].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[6];
              Bpieces[6].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else if (Bpieces[7].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[7];
              Bpieces[7].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Bpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[i];
                  Bpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Bpieces[i].type = BKNIGHT;
                  break;
                }
              }
            }
          } else {
            if (Wpieces[6].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[6];
              Wpieces[6].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else if (Wpieces[7].xy==0) {
              board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[7];
              Wpieces[7].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
            } else { /* promoted piece */
              for (i=8; i<16; i++) {
                if (Wpieces[i].xy==0) {
                  board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[i];
                  Wpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                  Wpieces[i].type = WKNIGHT;
                  break;
                }
              }
            } 
          }
          break;
        case 'P': 
          if (Xcolor==black) {
            for (i=8; i<16; i++) {
              if (Bpieces[i].xy==0) {
                board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Bpieces[i];
                Bpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                break;
              }
            }
          } else {
            for (i=8; i<16; i++) {
              if (Wpieces[i].xy==0) {
                board[10*(cbuf[2]-'1')+cbuf[1]-'a'+21] = &Wpieces[i];
                Wpieces[i].xy = 10*(cbuf[2]-'1')+cbuf[1]-'a'+21;
                break;
              }
            }
          }
          break;
        default: break;  
      }
    }
  }
  /* Fix non board piece pointers */
  for (PIECE *p=Bpieces[0].next; p!=NULL; p=p->next) {
    if (p->xy == 0) {
      p->prev->next = p->next;
      if (p->next)
        p->next->prev = p->prev;
    }
  }
  for (PIECE *p=Wpieces[0].next; p!=NULL; p=p->next) {
    if (p->xy == 0) {
      p->prev->next = p->next;
      if (p->next)
        p->next->prev = p->prev;
    }
  }
  /* castling flags reset*/  
  if (wking==E1) { 
    gflags &= ~1; /* wkmoved=0;*/
    gflags &= ~64; /* WHasCastled=0; */
  } else { 
    gflags |= 1;  /*  wkmoved=1; */
    gflags |= 64; /*  WHasCastled=1;*/
  }
  if (bking==E8) { 
    gflags &= ~8; /*  bkmoved=0; */
    gflags &= ~128; /*  BHasCastled=0;*/
  } else { 
    gflags |= 8; /*   bkmoved=1; */
    gflags |= 128; /*  BHasCastled=1;*/
  }
  if (board[A1]->type==WROOK) { gflags &= ~2; /*wra1moved=0;*/ } else { gflags |= 2; /*wra1moved=1;*/ }
  if (board[H1]->type==WROOK) { gflags &= ~4; /*wrh1moved=0; */} else { gflags |= 4; /*wrh1moved=1;*/ }
  if (board[A8]->type==BROOK) { gflags &= ~16; /*bra8moved=0;*/} else { gflags |= 16; /*bra8moved=1;*/}
  if (board[H8]->type==BROOK) { gflags &= ~32; /*brh8moved=0;*/} else { gflags |= 32; /*brh8moved=1;*/}
  EnPassantSq=0;  
  /* Move Stack Pointers reset */
  cst_p=0;
  mv_stack_p=0;
  HalfMovesPlayed=0;
  CurrentLine[0] = '\0';
  LoneKingReachedEdge=0;
  FiftyMoves=0;
  NotStartingPosition=1;
  PlayerMove.u=0;
}

void CheckSpecialDrawRules(void)
{
  int e, IsMaterialEnough;
  e = StaticEval(&IsMaterialEnough);
  if (IsMaterialEnough==0) {
    printf("1/2-1/2 {Draw. Not enough material.}\n");
  } else  if (HashRepetitions() == 3) {
    printf("1/2-1/2 {Draw by repetition}\n");
  } else if (FiftyMoves>=100) {
    printf("1/2-1/2 {Draw by fifty moves rule}\n");
  }
}

void CheckForMate(void)
{
  MOVE xmoves[MAXMV];
  int i, n, actual=0;
  if (side==white) {
    n=FindAllWhiteMoves(xmoves);
    for (i=0; i<n; i++) {
      PushStatus();
      MakeMove(&xmoves[i]);
      if (WhiteKingInCheck()) {
        RetractLastMove();
        PopStatus();
        continue;
      }
      RetractLastMove();
      PopStatus();
      actual++;
      break;
    }
    if (actual==0) {
      if (WhiteKingInCheck()) {
        printf("0-1 {Black Checkmates}\n");
      } else {
        printf("1/2-1/2 {Stalemate}\n");
      }
    }
  } else {
    n=FindAllBlackMoves(xmoves);
    for (i=0; i<n; i++) {
      PushStatus();
      MakeMove(&xmoves[i]);
      if (BlackKingInCheck()) {
          RetractLastMove();
          PopStatus();
          continue;
      }
      RetractLastMove();
      PopStatus();
      actual++;
      break;
    }
    if (actual==0) {
      if (BlackKingInCheck()) {
        printf("1-0 {White Checkmates}\n");
      } else {
        printf("1/2-1/2 {Stalemate}\n");
      }
    }
  }
}

#define AVERAGE_MOVE_NO 40

void xboard(void)
{
  char line[256], command[256];
  int moveNo=AVERAGE_MOVE_NO, TimeMins, Incr;
  int x_start_ply, protover;
  MOVE amove;
  side=white;
  ComputerSide=none;   /* no engine at start */
  max_time = 15000; /* by default 15 seconds/move */
  signal(SIGINT, SIG_IGN);
  printf("\n");
  for (;;) {
    fflush(stdout);
    if (side == ComputerSide) {
      if (side==white) {
        if (!GetWhiteBestMove(&amove)) {
          ComputerSide=none;
          continue;
        }
      } else {
        if (!GetBlackBestMove(&amove)) {
          ComputerSide=none;
          continue;
        }
      }
      printf("move %s\n",TranslateMoves(&amove));
      UpdateSpecialConditions(&amove);
      PushStatus();
      MakeMove(&amove);
      AddMoveToLine(amove.m.from,amove.m.to);
      CheckSpecialDrawRules();
      side = NextSide(side);
      CheckForMate();
      continue;
    } 
    if (!fgets(line, 256, stdin)) {
      return;
    }
    if (line[0] == '\n') {
      continue;
    }
    sscanf(line, "%s", command);
    if (!strcmp(command, "new")) {
      StartingPosition();
      side=white;
      ComputerSide=black;
      x_start_ply=mv_stack_p;
      continue;
    }
    if (!strcmp(command, "quit")){
      return;
    }
    if (!strcmp(command, "force")) {
      ComputerSide = none;
      continue;
    }
    if (!strcmp(command, "white")) {
      side = white;
      ComputerSide = black;
      x_start_ply=mv_stack_p;
      continue;
    }
    if (!strcmp(command, "black")) {
      side = black;
      ComputerSide = white;
      x_start_ply=mv_stack_p;
      continue;
    }
    if (!strcmp(command, "time")) {
      int l_move_p;
      if (ComputerSide==white) {
        l_move_p = mv_stack_p+1;
      } else if (ComputerSide==black) {
        l_move_p = mv_stack_p;
      }
      if (moveNo!=0) { /* Clasical time for n moves */
       if (l_move_p) {
        if (l_move_p%(2*moveNo) == 0 ) { /* clock start reset */
          x_start_ply=l_move_p;
        }
       }
       sscanf(line, "time %d", &max_time);
       max_time *= 10;
       if ((moveNo - (l_move_p - x_start_ply)/2)>0) {
         max_time /= (moveNo - (l_move_p - x_start_ply)/2);
       } else {
         max_time /= (AVERAGE_MOVE_NO - 10);
       }
      } else { /* Allocation with time per game and maybe increment */
       if (Incr) {
        if (l_move_p > ((2*AVERAGE_MOVE_NO)-10) ) {
          max_time = Incr*1000;
        }
       } else {
        if (l_move_p > ((3*AVERAGE_MOVE_NO)-10) ) {
          sscanf(line, "time %d", &max_time);
          max_time *= 10;        
          max_time /= (AVERAGE_MOVE_NO/2);
        }
       }
      }
      continue;
    }
    if (!strcmp(command, "post")) {
      Xoutput = _XBOARD_OUTPUT;
      continue;
    }
    if (!strcmp(command, "nopost")) {
      Xoutput = 0;
      continue;
    }
    if (!strcmp(command, "level")) {
      sscanf(line, "level %d %d %d", &moveNo, &TimeMins, &Incr);
      if (moveNo!=0) {
        max_time = TimeMins*60000/moveNo;
      } else {
        if (Incr) {
          max_time = TimeMins*60000/AVERAGE_MOVE_NO+Incr*1000;
        } else {
          max_time = TimeMins*60000/(2*AVERAGE_MOVE_NO);
        }
      }
      continue;
    }
    if (!strcmp(command, "hint")) {
      MOVE amove;
      if (side==white) {
        if (!GetWhiteBestMove(&amove))
          continue;
      } else {
        if (!GetBlackBestMove(&amove))
          continue;
      }
      printf("Hint: %s\n",TranslateMoves(&amove));
      continue;
    }
    if (!strcmp(command, "undo")) {
      RetractLastMove();
      PopStatus();
      side = NextSide(side);
      continue;
    }
    if (!strcmp(command, "remove")) {
      RetractLastMove();
      PopStatus();
      RetractLastMove();
      PopStatus();
      continue;
    }
    if (!strcmp(command, "go")) {
      ComputerSide = side;
      x_start_ply=mv_stack_p;
      continue;
    }
    if (!strcmp(command, "edit")) {
      ReadXboardPosition();
      continue;
    }
    if (!strcmp(command, "protover")) {
      sscanf(line, "protover %d", &protover);
      printf("feature time=1 done=1\n");
      continue;
    }
    if (!ParsePlayerMove(line,&amove,0)) {
      printf("Error (unknown command): %s\n", command);
    } else {
      PlayerMove.u = amove.u;
      UpdateSpecialConditions(&amove);
      PushStatus();
      MakeMove(&amove);
      AddMoveToLine(amove.m.from,amove.m.to);
      CheckSpecialDrawRules();
      side = NextSide(side);
      CheckForMate();
    }
  }
}

void Printmenu()
{
  printf("xboard - switch to XBoard mode\n");
  printf("play   - Play using Native console\n");
  printf("perft  - Performance test. (used also for Move Generation check) \n");
  printf("help   - displays a list of commands.\n");
  printf("bye    - exit the program\n");
}

/* -------  Main Function for NGplay Chess Engine -------- */

int main(int argc, char **argv)
{
  char s[256], book_s[256];
  Init_Pawn_Eval();
  printf("\n");
  MAX_TT  = 0x7fffff;
  PMAX_TT = (MAX_TT+1)/2-1;
  InitHash();
  strcpy(book_s,"NG3book.txt");
  StartingPosition();
  printf("\n--  %s Chess Engine  --\n", argv[0]);
  printf("Optional Run Time Usage: %s -p<positionFile> -b<BookFile> \n", argv[0]);
  if (argc>1) {
     int i;
     for (i=1; i<argc; i++) {
       if (argv[i][0]=='-' && argv[i][1]=='b') {
         strcpy(book_s, &(argv[1][2]));
       } 
       else if (argv[i][0]=='-' && argv[i][1]=='p') {
         ReadPosition(&(argv[1][2]));
       }
       else if (argv[i][0]=='-' && argv[i][1]=='h') {
       }
     }
  } 
  T_T = (struct tt_st *) calloc(MAX_TT+1, sizeof(struct tt_st));
  if (T_T==NULL) {
    printf("\nUnable to allocate Hash Table. Exiting.\n");
    exit(1);
  }
  Opp_T_T = (struct tt_st *) calloc(MAX_TT+1, sizeof(struct tt_st));
  if (Opp_T_T==NULL) {
    printf("\nUnable to allocate Hash Table. Exiting.\n");
    exit(1);
  }
  P_T_T = (struct ptt_st *) calloc(PMAX_TT+1, sizeof(struct ptt_st));
  if (P_T_T==NULL) {
    printf("\nUnable to allocate Pawn Hash Table. Exiting.\n");
    exit(1);
  }
  #ifdef DBGHASH
  printf("\n%u MBytes allocated for Hash Tables. Hash location size=%d bytes.\n\n",
         (unsigned int)(2*(MAX_TT+1)*sizeof(struct tt_st)/MByte), sizeof(struct tt_st));
  printf("\n%u MBytes allocated for Pawn Hash Tables. Hash location size=%d bytes.\n\n",
         (unsigned int)((PMAX_TT+1)*sizeof(struct ptt_st)/MByte), sizeof(struct ptt_st));
  #else
  printf("\nMemory allocated for Hash Tables.\n\n");
  #endif
  book_file = fopen(book_s, "r");
   if (!book_file)
     printf("Opening book missing.\n");
  printf("Commands available:\n\n");
  Printmenu();
  printf("\n");
  for (;;) {
    /* get user input */
    printf("> ");
    if (scanf("%s", s) == EOF)
      return 0;
    if (!strcmp(s, "bye")) {
      printf("Have a nice day!\n");
      break;
    }
    if (!strcmp(s, "xboard")) {
      Xoutput = _XBOARD_OUTPUT;
      xboard();
      break;
    }
    if (!strcmp(s, "play")) {
      Xoutput = _NORMAL_OUTPUT;
      ShowBoard();
      do {
        fprintf(stderr,"\nGive Computer Side (White = 1, Black = 2, None = 3) : ");
        scanf("%d",&ComputerSide);
      } while ((ComputerSide!=1) && (ComputerSide!=2) && (ComputerSide!=3));
      if (ComputerSide==2) ComputerSide=black;
      if (ComputerSide!=3) {
        fprintf(stderr,"Give Computer Time (seconds per move) : ");
        scanf("%d", &max_time);
        max_time *= 1000;
      }
      fprintf(stderr,"Game begins!\n");
      Play();
      break;
    }
    if (!strcmp(s, "perft")) {
      int SideToMove, start_depth, Use_hash=0;
      unsigned long long Presult;
      double tn;
      ShowBoard();
      do {
        fprintf(stderr,"Give Side to move (White = 1, Black = 2) : ");
        scanf("%d",&SideToMove);
      } while ((SideToMove!=1) && (SideToMove!=2));
      if (SideToMove==2) {
        SideToMove=black;
      }
      fprintf(stderr,"Give depth : ");
      scanf("%d",&start_depth);
      do {
        fprintf(stderr,"Use hash table : (yes = 1, no = 0) : ");
        scanf("%d",&Use_hash);
      } while ((Use_hash!=1) && (Use_hash!=0));
      start_time = GetMillisecs();
      Presult = Perft(start_depth, SideToMove, 1, Use_hash);
      tn = SECONDS_PASSED;
      fprintf(stderr,"\nPerft result = %llu nodes. Time used=%lf secs (%.0lf nodes/sec)", Presult, tn, floor(0.5+((double)Presult)/tn));
      break;
    }
    if (!strcmp(s, "help")) {
      Printmenu();
      continue;
    }
  }
  if (book_file)
    fclose(book_file);
  return 0;
}
