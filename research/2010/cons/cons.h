typedef unsigned long N;
typedef struct T {
   N hd;
   N tl;
} *T;

inline N tag(N x);
inline N unTag(N x);
inline int hasTag(N x);

inline N consN(N x,N y);
inline N hdN(N z);
inline N tlN(N z);

inline N consT(N x,N y);
inline N hdT(N z);
inline N tlT(N z);

inline N nil();
inline int isNil(N x);
inline N cons(N x,N y);
inline N hd(N z);
inline N tl(N z);
inline N ite(N x,N y,N z);

inline N incHd(N x);
inline N decHd(N x);

inline N succ(N x);
inline N pred(N x);
