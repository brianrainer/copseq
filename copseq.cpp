#include<bits/stdc++.h>
using namespace std;

#define mp make_pair
#define pb push_back
#define fi first
#define se second

typedef long long ll;
typedef pair<ll,ll> ii;

bool debug=true,testcase=true,rep=true;

const static int sieve_size=1e6+5, max_pow=64, max_n=1e3;
const static ll MOD=1e9+7;
bitset<sieve_size> is_prime;
vector<ll> d_sieve;  // divisors of num under sieve
ll combin[max_pow][max_pow];

unordered_map<ll,ll> pf,pf_powers;  //prime factors, prime factors powers
int id[max_n][max_pow];
ll pf_size,pf_pow_size,u_prime; // number of prime factors, unique numbering of pf
ll n,m,tc=1;

vector<vector<ll> > t_matrix,h_matrix,r_matrix;  // transition, helper, result matrix

ll mod_add(ll a, ll b, ll m){
	return ((a%m)+(b%m))%m;
}

ll mod_mult(ll a, ll b, ll m){
	ll r=0;
	while(b){
		if(b&1) r=mod_add(r,a,m);
		a=mod_add(a,a,m);
		b>>=1;
	} return r;
}

ll mod_exp(ll b, ll p, ll m){
	ll r=1;
	while(p){
		if(p&1) r=mod_mult(r,b,m);
		b=mod_mult(b,b,m);
		p>>=1;
	} return r;
}

void sieve(){
	is_prime.flip(); d_sieve.assign(sieve_size,1);
	is_prime.reset(0); is_prime.reset(1);
	int bound=sqrt(sieve_size);
	for(int i=2;i<bound;i++){
		if(is_prime.test(i)){
			for(int j=i*i;j<sieve_size;j+=i){
				d_sieve[j]=i;
				is_prime.reset(j);
	}}}
}

void combine(){
	memset(combin,0,sizeof(combin));
	for(int i=0;i<max_pow;i++){
		combin[i][0]=1;
		for(int j=1;j<=i;j++){
			combin[i][j]=mod_add(combin[i-1][j-1],combin[i-1][j],MOD);
	}}
	
	if(debug){
		for(int i=0;i<max_pow;i++){
			for(int j=0;j<max_pow;j++){
				cout<<combin[i][j]<<" ";
			} cout<<endl;
	}}
}

bool is_prima(ll p){
	if(p<sieve_size) return is_prime.test(p);
	if(p%2==0) return false;
	ll s=p-1;
	while(!(s&1)) s>>=1;
	ll a[10]={2,3,5,7,11,13,17,19,23,29};
	for(int i=0;i<10;i++){
		ll temp=s;
		ll mod=mod_exp(a[i],temp,p);
		while(temp!=p-1 && mod!=1 && mod!=p-1){
			mod=mod_mult(mod,mod,p);
			temp<<=1;
		}
		if(mod!=p-1 && temp%2==0) return false;
	}
	return true;
}

ll brent_pollard_rho(ll n){
	if(n<sieve_size) return d_sieve[n];
	ll sqrn=floor(sqrt(n));
	if((sqrn*sqrn)==n) return sqrn;
	
	srand(time(NULL));
	ll c,x,y,ys,d,r,q,k,m;
	y=(rand()%(n-2))+1;
	c=(rand()%(n-3))+2;
	d=r=q=1; m=1000;
	
	while(d==1) {
		x=y; k=0;
		for(int i=0;i<r;i++){ y=(mod_mult(y,y,n)+c)%m; }
		while(k<r && d==1) {
			ys=y;
			for(int i=0;i<min(m,r-k);i++){
				y = (mod_mult(y,y,n)+c)%n;
				q = mod_mult(q,abs(x-y),n);
			}
			d = __gcd(q,n);
			k+=m;
		} r<<=1;
	}
	if(d==n){
		do {
			ys = (mod_mult(ys,ys,n)+c)%n;
			d = __gcd(abs(x-ys),n);
		} while(d==1);
	}
	return d;
}

void factorize(ll m){
	while(m%2==0){ pf[2]++; m>>=1; }
	if (is_prima(m)){ pf[m]++; return; }
	
	ll f=brent_pollard_rho(m);
	if(f==1 || f==m) return;
	factorize(f); factorize(m/f);
}

void start_factorize(ll m){
	pf.clear();
	pf_powers.clear();
	pf_size=pf_pow_size=0;
	factorize(m);
}

void count_pow(){
	pf_size=pf_pow_size=1;
	for(auto p : pf){
		pf_powers[p.se]++;
		pf_size = mod_mult(pf_size,p.se+1,MOD);
	}
	
	for(auto p : pf_powers){
		pf_pow_size = mod_mult(pf_pow_size,p.se+1,MOD);
	}
	
	if(debug){
		for(auto p : pf){
			cout<<"("<<p.fi<<","<<p.se<<") ";
		} cout<<endl;
		for(auto p : pf_powers){
			cout<<"["<<p.fi<<","<<p.se<<"] ";	
		} cout<<endl;	
	}
}

void count_edge(){
	memset(id,0,sizeof(id));
	u_prime=0;	
	ll prev=1;
	for(auto p:pf_powers){
		for(int i=0;i<pf_pow_size;i++){
			id[i][u_prime]= (i/prev)%(p.se+1);
		} prev *= p.se+1; 
		id[0][u_prime]=p.fi; 
		u_prime++; 
	}
	
	t_matrix.assign(pf_pow_size, vector<ll>(pf_pow_size,0));
	for(int i=1;i<pf_pow_size;i++){
		for(int j=1;j<pf_pow_size;j++){
			ll inc,exc; inc=exc=1;
			for(int k=0;k<u_prime;k++){
				inc = mod_mult(inc,combin[pf_powers[id[0][k]]][id[j][k]],MOD);
				inc = mod_mult(inc,mod_exp(id[0][k],id[j][k],MOD),MOD);
				
				exc = mod_mult(exc,combin[pf_powers[id[0][k]]-id[i][k]][id[j][k]],MOD);
				exc = mod_mult(exc,mod_exp(id[0][k],id[j][k],MOD),MOD);
			}
			t_matrix[i][j]=(inc-exc+MOD)%MOD;
		}
	}
	
	if(debug){
		for(int i=0;i<pf_pow_size;i++){
			for(int j=0;j<u_prime;j++){
				cout<<id[i][j]<<" ";
			} cout<<endl;
		}
		for(int i=0;i<pf_pow_size;i++){
			for(int j=0;j<pf_pow_size;j++){
				cout<<t_matrix[i][j]<<" ";
			} cout<<endl;
		}
	}
}

void matrix_mult(vector<vector<ll> > &a, vector<vector<ll> > &b){
	ll res,size=a.size();
	h_matrix.assign(size,vector<ll>(size,0));
	for(int i=0;i<size;i++){
		for(int j=0;j<size;j++){
			res=0;
			for(int k=0;k<size;k++){
				res=mod_add(res,mod_mult(a[i][k],b[k][j],MOD),MOD);
			} h_matrix[i][j]=res;
	}}
	
	for(int i=0;i<size;i++){
		for(int j=0;j<size;j++){
			a[i][j]=h_matrix[i][j];
	}}
}

void matrix_exp(vector<vector<ll> > &a, ll p){
	ll size=a.size();
	r_matrix.assign(size,vector<ll>(size,0));
	for(int i=0;i<size;i++) r_matrix[i][i]=1;
	
	while(p){
		if(p&1) matrix_mult(r_matrix,a);
		matrix_mult(a,a);
		p>>=1;		
	}
	
	for(int i=0;i<size;i++){
		for(int j=0;j<size;j++){
			a[i][j]=r_matrix[i][j];
	}}
}

ll count_result(vector<vector<ll> >&a){
	ll ans=0,base_f;
	for(int i=1;i<a.size();i++){
		base_f=1;
		for(int j=0;j<u_prime;j++){
			base_f=mod_mult(base_f,combin[pf_powers[id[0][j]]][id[i][j]],MOD);
			base_f=mod_mult(base_f,mod_exp(id[0][j],id[i][j],MOD),MOD);
		}
		for(int j=1;j<a.size();j++){
			ans=mod_add(ans,mod_mult(base_f,a[i][j],MOD),MOD);
		}
	}	
	return ans;
}


int main(){
	debug=false;
	testcase=false;
	rep=false;
	
	combine(); sieve();
	
	ios_base::sync_with_stdio(false);
	
	if(testcase){
		cin>>tc;
	}
	while(tc--){
		cin>>n>>m;
		int rep_cnt=n;
		if (rep){
			rep_cnt=1;
		}
		for(;rep_cnt<=n;rep_cnt++){
			if (m==0){
				cout<<"0\n";
			} else if (m==1){
				if (n==1) cout<<"1\n"; else cout<<"0\n";
			} else if(is_prima(m)){
				if (!n) cout<<"0\n"; else if(n==1) cout<<"2\n"; else cout<<"1\n";
			} else {
				start_factorize(m);
				count_pow();
				
				if (n==1){
					cout<<pf_size<<endl;
				} else {
					count_edge();
					matrix_exp(t_matrix,n-1);
					ll ans=count_result(t_matrix);
					cout<<ans<<endl;
				}
			}
		}
	}
		
	return 0;
}
