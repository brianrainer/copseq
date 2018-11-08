#include<bits/stdc++.h>
using namespace std;

#define pb push_back
#define mp make_pair
#define fi first
#define se second

typedef long long ll;
typedef pair<int, int> ii;

const bool DEBUG = true;

ll mulmod(ll multa, ll multb, ll mod){
	ll res=0ll; multa%=mod;
	while(multb){
		if(multb&1) res=(res+multa)%mod;
		multa=(multa<<1)%mod;
		multb>>=1;
	}
	return res;
}

ll fast_gcd(ll a, ll b){
	while(true){
		ll r=a%b;
		if (r==0) return b;
		a=b; b=r;
	}
}

ll fast_exp(ll base, ll pow, ll mod){
	ll res=1ll;
	while(pow){
		if (pow&1) res=mulmod(res, base, mod);
		base = mulmod(base, base, mod);
		pow>>=1;
	}
	return res;
}

bool millerRabin(ll p){
	if (p<2 || (p!=2 && p%2==0)) return false;
	ll s=p-1;
	while(s%2==0) s>>=1;
	ll a[10] = {2,3,5,7,11,13,17,19,23,29}; 
	for(int i=0;i<10;i++){
		ll temp=s;
		ll mod=fast_exp(a[i],temp,p);
		while(temp!=p-1 && mod!=1 && mod!=p-1){
			mod = mulmod(mod,mod,p);
			temp<<=1;
		}
		if (mod!=p-1 && temp%2==0) return false;
	}
	return true;
}

ll floyd_pollard_rho(ll n){
	ll d=n;
	for(int c=2; d==n; c++){
		ll x=2;
		ll y=x;
		while(true) {
			x = (mulmod(x,x,n) + c)%n;
			y = (mulmod(y,y,n) + c)%n;
			y = (mulmod(y,y,n) + c)%n;
			d = fast_gcd(abs(x-y),n);
			if(d>1) break;
		}
	}
	return d;
}

ll brent_pollard_rho(ll n){
	if (n<2) return 1;
	if (n%2==0) return 2;

	srand(time(NULL));
	ll c,x,y,ys,d,r,q,k,m;
	y=(rand()%(n-0))+0;
	do { c=(rand()%(n-3))+1; } while(y==c);
	d=r=q=1; m=1000;
	
	while(d==1) {
		x=y;
		for (int i=0;i<r;i++){
			y = (mulmod(y,y,n) + c)%n;
		}
		k=0;
		while(k<r && d==1) {
			ys=y;
			for(int i=0;i<min(m,r-k);i++){
				y = (mulmod(y,y,n) + c)%n;
				q = mulmod(q,abs(x-y),n);
			}
			d = fast_gcd(q,n);
			k+=m;
		}
		r<<=1;
	}
	if(d==n){
		while(true) {
			ys = (mulmod(ys,ys,n) + c)%n;
			d = fast_gcd(abs(x-ys),n);
			if (d>1) break;
		}
	}
	return d;
}

const static int sie_sz = 1e6+5;
bitset<sie_sz> is_prime;
vector<ll> divs(sie_sz, 1);
void sieve(){
	is_prime.flip(); 
	is_prime.reset(0); is_prime.reset(1);
	for(int i=2;i<sqrt(sie_sz);i++){
		if(is_prime.test(i)){
			for(int j=i*i;j<sie_sz;j+=i){
				divs[j]=i;
				is_prime.reset(j);
	}}}
}

bool probablyPrime(ll n){
	if(n<sie_sz){
		return is_prime.test(n);
	} else {
		return millerRabin(n);
	}
}


vector<ll> ndivs;
void factorize(ll n){
	// cout<<"fac"<<n<<" ";
	if (n==1) return;

	while(n%2==0){
		ndivs.pb(2);
		n>>=1;
	}

	if(probablyPrime(n)) {
		ndivs.pb(n);
		return;
	}

	ll d;
	if (n<sie_sz){
		d = divs[n];
	} else {
		d = brent_pollard_rho(n);
	}

	if (d!=1 && d!=n) {	
		factorize(d);
		factorize(n/d);
	}
}

void start_factorize(ll n){
	ndivs.clear();
	factorize(n);
	if (DEBUG){
		if (ndivs.empty()){ cout<<"1"<<endl; } 
		else { 
			sort(ndivs.begin(), ndivs.end());
			for(int i=0;i<ndivs.size();i++){ cout<<ndivs[i]<<" "; } 
			cout<<endl;
	}}
}

int main(){
	sieve();
	
	ll n,m;
	cin>>n; 
	while(n--){
		cin>>m; start_factorize(m);
	}

	return 0;
}