# 模板补录

## 列表

1. 多项式半个全家桶（大常数但好写版本）。
2. `unordered_map` 自定义哈希。
3. 优选法求单峰函数最值，替代三分。
4. 严格 wqs 二分。
5. 决策单调性分治优化分段 DP，可莫队类 cdq 版本。
6. 杜教筛。PN 筛。
7. Min-Max 容斥。
8. 类欧几里得。
9. 同余方程通解和剩余定理。

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
    uint32_t w;
    modInt (int _w=0) { 
        int t = _w % p;
        if (t < 0) t += p;
        w = (uint32_t)t;
    }
    inline modInt& operator+=(const modInt &a) {
        uint32_t x = w + a.w;
        if (x >= (uint32_t)p) x -= p;
        w = x;
        return *this;
    }
    inline modInt& operator-=(const modInt &a) {
        uint32_t x = (w >= a.w) ? (w - a.w) : (w + (uint32_t)p - a.w);
        w = x;
        return *this;
    }
    inline modInt& operator*=(const modInt &a) {
        w = (uint32_t)((uint64_t)w * a.w % p);
        return *this;
    }
    friend inline modInt operator + (modInt a, const modInt &b) { a += b; return a; }
    friend inline modInt operator - (modInt a, const modInt &b) { a -= b; return a; }
    friend inline modInt operator * (modInt a, const modInt &b) { a *= b; return a; }
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

### 杜教筛PN筛

$$F*G=H$$

$$F[1]S_G(n)=S_H(n)-\sum_{d=2}^nF[d]\cdot S_G(\lfloor\frac{n}{d}\rfloor)$$

$$\begin{align*}
    \varphi * I &= id \\
    \mu * I &= e \\
    I * I &= \sigma
\end{align*}$$

PN 筛：

$F*G=H$ ，令 $G$ 在质数处和 $F$ 等值，G 积性，则 H 只在 PN 处取值，G 需要可快速前缀和（杜教筛）。

$$\begin{align*}
    \sum_i^n F &=\sum_i\sum_{d|i} H(d)\cdot G(\frac{i}{d})\\
    &=\sum_dH(d) \sum_{i=1}^{\lfloor n/d\rfloor} G(i)
\end{align*}$$

复杂度 $O(n^\frac{2}{3})$ （需要提前筛出前面的值）

求 $H(p^c)$：

$$F(p^c)=\sum_{i=0}^c H(p^i)G(p^{c-i})$$

这个代码求 $F(p^k)=p^k(p^k-1),G(p)=p\varphi(p)=id\cdot \varphi$ 。

$$(\varphi \cdot id)*id=id_2$$

```cpp
#include<bits/stdc++.h>
using namespace std;
const int N=2e6+10;
typedef long long ll;
const ll p=1e9+7;

ll h[N][40]; bool vis[N][40];
int pri[N],top; bool ispri[N];
ll phi[N];
ll G[N];
ll inv2,inv6,n;
ll qpow(ll a,ll b) {
    ll ans=1,base=a;
    while(b>0) {
        if(b&1) ans=ans*base%p;
        base=base*base%p;
        b>>=1;
    }
    return ans;
}

void sieve() {
    phi[1]=1;
    for(int i=2;i<N;i++) {
        if(!ispri[i]) {
            pri[++top]=i;
            phi[i]=i-1;
            h[top][0]=1; h[top][1]=0;
            vis[top][0]=vis[top][1]=1;
        }
        for(int j=1;j<=top&&1ll*i*pri[j]<N;j++) {
            ispri[i*pri[j]]=1;
            if(i%pri[j]==0) {
                phi[i*pri[j]]=phi[i]*pri[j];
                break;
            }
            phi[i*pri[j]]=phi[i]*(pri[j]-1);
        }
    }
    for(int i=1;i<N;i++) {
        G[i]=G[i-1]+1ll*i*phi[i]%p;
        G[i]%=p;
    }
    inv2=qpow(2,p-2); inv6=qpow(6,p-2);
}
unordered_map<ll,ll>sg;
ll sum(ll n) {
    ll mn=n%p;
    return mn*(mn+1)%p*inv2%p;
}
ll calcG(ll n) {    
    if(n<N) return G[n];
    if(sg.count(n)) return sg[n];
    ll mn=n%p; 
    ll ans=mn*(mn+1)%p*(2*mn+1)%p*inv6%p;
    for(ll l=2,r;l<=n;l=r+1) {
        r=n/(n/l);
        ans-=((sum(r)-sum(l-1))*calcG(n/l)%p);
        ans%=p;
    }
    ans=(ans%p+p)%p;
    sg[n]=ans;
    return ans;
}

ll ans;
void solve(ll hval,ll hv,int now) {
    ans=(ans+hval*calcG(n/hv)%p)%p;
    for(int i=now;i<=top;i++) {
        if(i>1&&hv>n/pri[i]/pri[i]) break;
        for(ll x=1ll*hv*pri[i]*pri[i],c=2;x<=n;x=x*pri[i],c++) {
            if(!vis[i][c]) {
                vis[i][c]=1;
                ll f=qpow(pri[i],c);
                f=f*(f-1)%p;
                ll g=1ll*pri[i]*(pri[i]-1)%p;
                ll t=1ll*pri[i]*pri[i]%p;
                for(int j=1;j<=c;j++) {
                    f-=g*h[i][c-j]%p;
                    g=g*t%p;
                    f=(f%p+p)%p;
                }
                h[i][c] = f;
            }
            if(h[i][c]) solve(hval*h[i][c]%p,x,i+1);
        }
    }
}

int main(){
    sieve();
    scanf("%lld",&n);
    solve(1,1,1);
    printf("%lld\n",ans);
}
```

### Min-Max 容斥


$$\min(S)=\sum_{T \subseteq S} (-1)^{|T|+1} \max(T)$$

$$\max(S)=\sum_{T \subseteq S} (-1)^{|T|+1} \min(T)$$

$$\operatorname{kthmax(S)}=\sum_{T \subseteq S} (-1)^{|T|-k} \binom{|T|-1}{k-1} \min(T)$$

### 类欧几里得

$y=\lfloor \frac{ax+b}{c}\rfloor$ 。

求 $\sum y,\sum y^2,\sum xy$

```cpp
#include<bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll p=998244353;

struct node{
    ll cntx,cnty,sumx,sumy,power,prod;
    node(){cntx=cnty=sumx=sumy=power=prod=0;}
    node operator * (const node b)
    {
        node ans;
        ans.cntx=cntx+b.cntx; ans.cntx%=p;
        ans.cnty=cnty+b.cnty; ans.cnty%=p;
        ans.sumx=sumx+b.sumx+cntx*b.cntx%p; ans.sumx%=p;
        ans.sumy=sumy+b.sumy+cnty*b.cntx%p; ans.sumy%=p;
        ans.power=power+b.cntx*cnty%p*cnty%p+2ll*cnty*b.sumy%p+b.power; ans.power%=p;
        ans.prod=prod+b.cntx*cntx%p*cnty%p+cntx*b.sumy%p+cnty*b.sumx%p+b.prod; ans.prod%=p;
        return ans;
    }
};

node qpow(node a,ll b)
{
    node ans,base=a;
    while(b>0)
    {
        if(b&1) ans=ans*base;
        base=base*base;
        b>>=1;
    }
    return ans;
}

node solve(ll p,ll q,ll r,ll n,node U,node R)
{
    if(!n) return node();
    if(r>=q) return qpow(U,r/q)*solve(p,q,r%q,n,U,R);
    if(p>=q) return solve(p%q,q,r,n,U,qpow(U,p/q)*R);
    ll m=(p*n+r)/q;
    if(!m) return qpow(R,n);
    ll cnt=n-(q*m-r-1)/p;
    return qpow(R,(q-r-1)/p)*U*solve(q,p,(q-r-1)%p,m-1,R,U)*qpow(R,cnt);
}

int T; ll n,a,b,c;

int main()
{
    scanf("%d",&T);
    while(T--)
    {
        scanf("%lld%lld%lld%lld",&n,&a,&b,&c);
        node U,R;
        U.cnty=1; R.cntx=1;
        R.sumx=1;
        node ans=solve(a,c,b,n,U,R);
        ll w1=ans.sumy,w2=ans.power,w3=ans.prod;
        w2+=(b/c)*(b/c); w2%=p;
        w1+=b/c; w1%=p;
        printf("%lld %lld %lld\n",w1,w2,w3);
    }
}
```

### 同余方程通解

$$ax+yn=b$$

$k=\frac{b}{\gcd(a,n)}$ ，此时的通解形式为：（设 $x_0,y_0$ 是对 $\gcd(a,b)$ 的特解）

$$x=kx_0+\frac{n}{d}t,y=ky_0-\frac{a}{d}t$$

剩余定理：

$$\left\{ 
    \begin{aligned}
    x &\equiv a_1 \bmod n_1\\
    x &\equiv a_2 \bmod n_2\\
    &\cdots\\
    x &\equiv a_m \bmod n_m
\end{aligned}
\right.
$$

这里 $n_1,n_2,\cdots,n_m$ 不一定互质。

将两个方程合并成一个。

转化成：$x=n_1p+a_1=n_2q+a_2$ ，就有 $n_1p-n_2q=a_2-a_1$ ，可以用扩展欧几里得解出其特解 $(p,q)$ 及 $x_0$ ，此时 $\operatorname{lcm(n_1,n_2)}$ 构成最小正周期，通解为：

$$x_0+t\operatorname{lcm(n_1,n_2)}$$

这里取 $x$ 的任意一个等式作为合并方程：

$$x\equiv (n_1p+a_1) \bmod \operatorname{lcm(n_1,n_2)}$$

最终合并成一个方程即可。