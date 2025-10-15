# 模板补录

## 列表

1. 多项式半个全家桶（大常数但好写版本）。
2. `unordered_map` 自定义哈希。
3. 优选法求单峰函数最值，替代三分。
4. 严格 wqs 二分。
5. 决策单调性分治优化分段 DP，可莫队类 cdq 版本。

## 内容

### 多项式

```cpp
#include<bits/stdc++.h>
using namespace std;
const int N=4e5+10;
const int p=998244353;
const int rsp=3;

struct poly;
void change(poly &a);
void ntt(poly &a,int op);

struct modInt {
    int w;
    modInt (int _w=0):w(_w%p) {}
    inline modInt operator + (const modInt &a) const {
        if(w+a.w>=p) return w+a.w-p;
        else return w+a.w;
    }
    inline modInt operator - (const modInt &a) const {
        if(w-a.w<0) return w-a.w+p;
        else return w-a.w;
    }
    inline modInt operator * (const modInt &a) const {
        return 1ll*w*a.w%p;
    }
};
inline modInt qpow(modInt a,int b ) {
    modInt ans=1,base=a;
    while(b>0) {
        if(b&1) ans=ans*base;
        base=base*base;
        b>>=1;
    }
    return ans;
}

modInt fac[N],inv[N],intinv[N];
modInt invrsp;
int lg[N];
void valinit() {
    fac[0]=inv[0]=1;
    for(int i=1;i<N;i++) fac[i]=fac[i-1]*i,intinv[i]=qpow(i,p-2);
    for(int i=2;i<N;i++) lg[i]=lg[i/2]+1;
    inv[N-1]=qpow(fac[N-1],p-2);
    for(int i=N-2;i>=1;i--) inv[i]=inv[i+1]*(i+1);
    invrsp=intinv[rsp];
}

struct poly {
    vector<modInt>v;
    poly(modInt w=0):v(1){v[0]=w;}
    poly(const vector<modInt>&w):v(w){}
    modInt operator [](int x) const {return x>=(int)v.size()?0:v[x];}
    modInt& operator [] (int x) {
        if(x>=(int)v.size()) v.resize(x+1);
        return v[x];
    }
    int size() const {return v.size();}
    void resize(int x) {v.resize(x);}
    poly slice(int len) {
        if(len<=(int)v.size()) return vector<modInt>(v.begin(),v.begin()+len);
        vector<modInt>ret(v); ret.resize(len);
        return ret;
    }
    poly operator * (const modInt &x) {
        poly ret(v);
        for(int i=0;i<(int)v.size();i++) ret[i]=ret[i]*x;
        return ret; 
    }
    poly operator * (const poly &G) {
        poly f(v),g=G;
        int rec=f.size()+g.size()-1;
        int len=1<<(lg[rec]+1);
        f.resize(len),g.resize(len);
        ntt(f,1); ntt(g,1);
        for(int i=0;i<len;i++) f[i]=f[i]*g[i];
        ntt(f,-1);
        return f.slice(rec);
    }
    poly operator - (const poly &G) {
        poly f(v),g=G;
        int d=max(f.size(),g.size());
        poly rec(d);
        for(int i=0;i<d;i++) rec[i]=f[i]-g[i];
        return rec;
    }
    poly operator + (const poly &G) {
        poly f(v),g=G;
        int d=max(f.size(),g.size());
        poly rec(d);
        for(int i=0;i<d;i++) rec[i]=f[i]+g[i];
        return rec;
    }
}; 

void change(poly &a) {
    vector<int>rev(a.size());
    for(int i=0;i<a.size();i++) {
        rev[i]=rev[i>>1]>>1;
        if(i&1) rev[i]|=(a.size()>>1);
    }
    for(int i=0;i<a.size();i++) {
        if(i<rev[i]) swap(a[i],a[rev[i]]);
    }
}
inline void ntt(poly &a,int op) {
    change(a); int len=a.size();
    for(int h=2;h<=len;h<<=1) {
        modInt step=qpow((op==1)?rsp:invrsp,(p-1)/h);
        for(int j=0;j<len;j+=h) {
            modInt w=1;
            for(int k=j;k<j+h/2;k++) {
                modInt u=a[k],v=w*a[k+h/2];
                a[k]=u+v; a[k+h/2]=u-v;
                w=w*step;
            }
        }
    }
    if(op==-1) {
        modInt iv=qpow(len,p-2);
        for(int i=0;i<len;i++) a[i]=a[i]*iv;
    }
}

inline poly inverse(poly f,int len) {
    poly g(qpow(f[0],p-2));
    int k=1;
    while(k<len) {
        k<<=1;
        g=g*(poly(2)-g*f.slice(k));
        g=g.slice(k);
    }
    return g.slice(len);
}
inline poly derive(poly f) {
    int len=f.size();
    for(int i=0;i<len-1;i++) f[i]=f[i+1]*(i+1);
    return f.slice(len-1);
}
inline poly intger(poly f) {
    int len=f.size()+1;
    f=f.slice(len);
    for(int i=len-1;i>=1;i--) f[i]=f[i-1]*intinv[i];
    f[0]=0;
    return f;
}
inline poly log(poly f,int len) {
    poly g=derive(f)*inverse(f,len);
    return intger(g).slice(len);
}
inline poly exp(poly f,int len) {
    poly g(1);
    int k=1;
    while(k<len) {
        k<<=1;
        g=g*(poly(1)-log(g,k)+f.slice(k));
        g=g.slice(k);
    }
    return g.slice(len);
}

int n,a[N];

int main() {
    valinit();
    scanf("%d",&n);
    poly f;
    f.resize(n);
    for(int i=0;i<n;i++) scanf("%d",&a[i]),f[i]=a[i];
    poly g=log(f,n);
    for(int i=0;i<n;i++) printf("%d ",g[i].w);
}
```

### 自定义哈希

```cpp
#include<bits/stdc++.h>
using namespace std;

struct custom_hash {
    static uint64_t splitmix64(uint64_t x) {
        x += 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
        x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
        return x ^ (x >> 31);
    }

    size_t operator()(uint64_t x) const {
        static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x + FIXED_RANDOM);
    }
};

unordered_map<int, int, custom_hash> mp;

int main() {

}
```

### 优选法（黄金分割）

其迭代次数比三分快，且复用节点能少一半常数，求凸函数时也比二分法正确。

```cpp
const db gor=(sqrt(5)-1.0)/2.0;
double solve() {
    db l=-1e5,r=1e5;
    bool kl=0,kr=0;
    db w1,w2,m1,m2;
    while(r-l>eps) {
        db len=(r-l)*gor;
        if(!kl) {
            m1=r-len; w1=calc(m1);
            kl=1; 
        }
        if(!kr) {
            m2=l+len; w2=calc(m2);
            kr=1;
        }
        if(w1<w2) {
            l=m1; m1=m2; w1=w2;
            kl=1; kr=0;
        }
        else {
            r=m2; m2=m1; w2=w1;
            kl=0; kr=1;
        }
    }
    return calc((r+l)/2.0);
}
```

### 严谨 wqs 二分

传统 wqs 二分有诸多问题，这里有一个严格的，可运用多维的。

- 若 $f(x)$ 上凸，设 $g(k)=\max_x(f(x)-kx)+ka$ ，则 $g(k)$ 下凸，且最值 $\min(g(k))=f(a)$ 。

- 若 $f(x)$ 下凸，设 $g(k)=\min_x(f(x)-kx)+ka$ ，则 $g(k)$ 上凸，且最值 $\max(g(k))=f(a)$ 。

这样就转化成了求凸函数最值，且支持多维度逐次拆分。

求解 $g(k)$ 最值用常规 dp 加上惩罚，且转化了问题，不用记录段数判断。

### 分治决策单调性

若使用 `wqs` ，惩罚加在 `cost` 里。

若需要记录段数，`chkmax` 里额外判断，以 `f` 为第一关键字，**`cnt` 为第二关键字**。

```cpp
void chkmax(int i,int j) {
    db w=f[j]+cost(j,i);
    if(w<f[i]&&f[i]-w>eps) f[i]=w,las[i]=j;
}

void dfs(int l,int r) {
    if(r-l==1) return;
    int mid=(l+r)>>1;
    for(int i=las[l];i<=las[r];i++) chkmax(mid,i);  
    dfs(l,mid);
    for(int i=l+1;i<=mid;i++) chkmax(r,i);
    dfs(mid,r);
}

double calc(db k) {
    for(int i=1;i<=n;i++) f[i]=inf,las[i]=0;
    f[0]=0; 
    pen=k;
    chkmax(n,0);
    dfs(0,n);
    return f[n]+k*m;
}
```