#include<bits/stdc++.h>
using namespace std;

#define pb push_back
#define mp make_pair
#define fi first
#define se second

typedef unsigned long long ll;
typedef pair<ll,ll> ii;

bool DEBUG = true;
bool TESTCASES = true;
ll MODULO = 1e9+7;

ll mulmod(ll multa, ll multb, ll mod){
	return ((multa%mod)*(multb%mod))%mod;
	
//	ll res=0ll; multa%=mod;
//	while(multb){
//		if(multb&1) res=(res+multa)%mod;
//		multa=(multa<<1)%mod;
//		multb>>=1;
//	}
//	return res;
}

ll fast_gcd(ll a, ll b){
	return __gcd(a,b);
	
//	while(true){
//		ll r=a%b;
//		if (r==0) return b;
//		a=b; b=r;
//	}
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
	d=r=q=1; m=100;
	
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

unordered_map<ll,int> divisors;
void factorize(ll n){
	if (n<2) return;
	while(n%2==0){ divisors[2]++; n>>=1; }
	if(probablyPrime(n)) { divisors[n]++; return; }

	ll d;
	if (n<sie_sz){ d = divs[n]; } 
	else { d = brent_pollard_rho(n); }

	if (d!=1 && d!=n) {	
		factorize(d); 
		factorize(n/d); 
	}
}

ll matrix_mult(vector<ll> &a, vector<ll> &b){
	ll r=0;
	for(int i=0;i<a.size();i++){
		r = (r+mulmod(a[i],b[i],MODULO))%MODULO;
	} return r;
}

void matrix_mult(vector<ll> &a, vector<vector<ll> > &b){
	ll res,tmp;
	vector<ll> c;
	for (int i=0;i<a.size();i++){
		res=0;
		for(int j=0;j<a.size();j++){
			tmp = mulmod(a[j], b[i][j], MODULO);
			res = (res+tmp)%MODULO;
		} c.pb(res);
	}
	
	for(int i=0;i<a.size();i++){
		a[i]=c[i];
	}
}

void matrix_mult(vector<vector<ll> > &a, vector<vector<ll> > &b){
	ll res,tmp;
	vector<ll> d;
	vector<vector<ll> > c;
	
	for (int i=0;i<a.size();i++){
		d.clear(); 
		for(int j=0;j<a.size();j++){
			res=0;
			for(int k=0;k<a.size();k++){
				tmp = mulmod(a[i][k], b[k][j], MODULO);
				res = (res+tmp)%MODULO;
			} d.pb(res);
		} c.pb(d);
	}
	
	for(int i=0;i<a.size();i++){
		for(int j=0;j<a.size();j++){
			a[i][j]=c[i][j];
		}
	}
}

void matrix_exp(vector<vector<ll> > &a, ll pow){
	if (pow==0) return;	
	
	vector<ll> d;
	vector<vector<ll> > c;
	
	for(int i=0;i<a.size();i++){
		d.clear();
		for(int j=0;j<a.size();j++){
			d.pb(a[i][j]);			
		} c.pb(d);
	}
	
	while(pow){
		if (pow&1) matrix_mult(a,c);
		matrix_mult(c,c);
		pow>>=1;
	}
}



void start_factorize(ll num){
	divisors.clear();
	factorize(num);
	
	if (DEBUG){
//		cout<<divisors.size()<<endl;
		for(auto d : divisors){
			cout<<"("<<d.fi<<","<<d.se<<")"<<" ";
		} cout<<endl;
	}
}

const int maxn=1e3,pow_size = 63;
ll ukuran;
ll combin[pow_size][pow_size];
ll i_stack[pow_size];
ll i_matrix[maxn][pow_size];
ll i_prima[pow_size];
void fill_stack(int depth){
	if (depth==pow_size){
		int i;
		for(i=1;i<pow_size;i++){
			i_matrix[ukuran][i] = i_stack[i];		
		} 
		if (false)
		if (DEBUG){
			cout<<ukuran<<" "<<i<<endl;	
			for(int i=0;i<pow_size;i++){
				cout<<i_matrix[ukuran][i]<<" ";
			} cout<<endl;
			system("pause");
		}
		ukuran++;
		return;
	}
	
	for(i_stack[depth]=0;i_stack[depth]<=i_prima[depth];i_stack[depth]++){
		fill_stack(depth+1);
	}
}

vector<vector<ll> > t_matrix;
void prepare_combin(){
	memset(combin,0,sizeof(combin));
	memset(i_stack,0,sizeof(i_stack));
	memset(i_matrix,0,sizeof(i_matrix));
	ukuran=0;
	for(int i=0;i<pow_size;i++){
		combin[i][0]=1;
		for(int j=1;j<=i;j++){
			combin[i][j] = (combin[i-1][j-1]+combin[i-1][j])%MODULO;
		}
	}
	
	fill_stack(0);

	if (DEBUG){
		if (false)
		for(int i=0;i<pow_size;i++){
			for(int j=0;j<pow_size;j++){
				cout<<combin[i][j]<<" ";
			} cout<<endl;
		}
		
		if (false)
		for(int i=0;i<ukuran;i++){
			for(int j=0;j<pow_size;j++){
				cout<<i_matrix[i][j]<<" ";
			} cout<<endl;
		}
	}
	
	t_matrix.assign(ukuran+5, vector<ll>(ukuran+5,0));
	for(int i=1;i<ukuran;i++){
		for(int j=1;j<ukuran;j++){
			ll P,Q; P=Q=1;
			if (false)
			if (DEBUG){
				cout<<i<<" "<<j<<" : ";
			}
			ll tmpf, tmpg;
			for(int k=1;k<pow_size;k++){
				tmpf = mulmod(combin[i_prima[k]][i_matrix[j][k]] , fast_exp(k,i_matrix[j][k],MODULO) , MODULO);
				P = mulmod(P,tmpf,MODULO);
				
				tmpg = mulmod(combin[i_prima[k]-i_matrix[i][k]][i_matrix[j][k]] , fast_exp(k,i_matrix[j][k],MODULO) , MODULO);
				Q = mulmod(Q,tmpg,MODULO);
			}
			t_matrix[i][j]=(P+MODULO-Q)%MODULO;
		}
	}
	
	if (DEBUG)
	for(int i=0;i<ukuran;i++){
		for(int j=0;j<ukuran;j++){
			cout<<t_matrix[i][j]<<" ";
		} cout<<endl;
	}
}

void calculate_final_v3(ll pow){
	memset(i_prima,0,sizeof(i_prima));
	for (auto d : divisors){
		i_prima[d.se]++;
	}
	
	if (DEBUG){
		for(int i=0;i<pow_size;i++){
			cout<<i_prima[i]<<" ";
		} cout<<endl;
	}
}

void calculate_final_v2(ll pow){	
	vector<ii> work(divisors.begin(), divisors.end());
	sort(work.begin(), work.end());
	
	int size=(1<<divisors.size());
	vector<ll> base(size,0);
	vector<ll> dp(size,0);
	vector<ll> identityD(size,1);
	
	for(int i=0;i<size;i++){
		int j=i,k=0;
		ll cnt=1;
		while(j){
			if(j&1){
				cnt = mulmod(cnt,work[k].se,MODULO);
			} k++; j>>=1;
		} dp[i]=cnt;
	} dp[0]=0;
	base = dp;
	
	vector<ll> helperZ;
	for(int k=0;k<pow-1;k++){
		helperZ.clear();
		for(int i=0;i<size;i++){
			ll tmprd=base[i],tmpre=0;
			for(int j=0;j<size;j++){
				if (i&j){
					tmpre = (tmpre+dp[j])%MODULO;
//					tmprd = (tmprd+base[j])%MODULO;
//					tmprd = mulmod(tmprd, base[j], MODULO);
				}
			} tmprd = mulmod(tmprd,tmpre,MODULO);
			helperZ.pb(tmprd);
		} dp = helperZ;
		
		if (DEBUG){
			for(int z=0;z<size;z++){
				cout<<dp[z]<<" ";
			} cout<<endl;
		}
	}
	
	ll final_ans = matrix_mult(dp, identityD);
	if (pow==1) final_ans++;
	cout<<final_ans<<endl;
}

void calculate_final(ll pow){
	// move to vector for dependable indexing
	vector<ii> work(divisors.begin(), divisors.end());
	sort(work.begin(), work.end());
	
	int size=(1<<divisors.size());
	vector<ll> identityA(size,1); identityA[0]=0;
	vector<ll> identityB(size,1); identityB[0]=0;
	vector<ll> dp(size,0);
	
	// memo each divisors count
	for(int i=0;i<size;i++){
		int j=i,k=0;
		ll cnt=1;			
		while(j){
			if (j&1){
//				cnt = cnt*work[k].se;
				cnt = mulmod(cnt, work[k].se, MODULO);
			} k++; j>>=1;
		} dp[i]=cnt;
		
		if (DEBUG) cout<<dp[i]<<" ";
	} if (DEBUG) cout<<endl;
	dp[0]=0;
	
	// build the matrix
	vector<ll> vxx(size,0);
	vector<vector<ll> > matrix(size,vxx);
	for(int i=0;i<size;i++){
		ll tempr=0;
		for(int j=0;j<size;j++){
//			matrix[i][j] = (i&j? dp[i]*dp[j] : 0);
			matrix[i][j] = (i&j? mulmod(dp[i],dp[j],MODULO) : 0);
			tempr = (i&j? tempr+matrix[i][j] : tempr);
			tempr %= MODULO;
		}
		vxx[i] = tempr;
	}
	
	if (DEBUG){
		cout<<"tempra\n";
		for(int i=0;i<size;i++){
			cout<<vxx[i]<<" ";			
		} cout<<endl;
	}
	
	ll final_ans=0;
	if (pow==1){
		final_ans=matrix_mult(dp,identityB);
	} else if (dp.size()==2){
		final_ans = fast_exp(dp[1],pow,MODULO);	
	} else if(pow==2){
		if (DEBUG){
			for(int i=1;i<matrix.size();i++){
				for(int j=1;j<matrix.size();j++){
					cout<<matrix[i][j]<<" ";
				} cout<<endl;
			}
		}
		
		matrix_mult(identityA, matrix);
		final_ans=matrix_mult(identityA, identityB);
	} else {
		vector<ll> helperC;
		for(int npow=0;npow<pow-2;npow++){
			helperC.clear();
			for(int i=0;i<size;i++){
				ll tmpra=0;
				for (int j=0;j<size;j++){
					tmpra = (i&j? tmpra+vxx[j]:tmpra); 
					tmpra %= MODULO;
				} helperC.pb(tmpra);
			}
			vxx = helperC;
		}
		
		if (DEBUG){
			cout<<"tempru\n";
			for(int i=0;i<size;i++){
				cout<<vxx[i]<<" ";
			} cout<<endl;
		}
		
		final_ans = matrix_mult(dp, vxx);
	}
	cout<<final_ans<<endl;

}

void unit_test(){	
	vector<ll> v(3,1);
	vector<vector<ll> > test(3,v);
	for(int i=0;i<3;i++) test[i][i]=0;
	matrix_exp(test,1);
	for(int i=0;i<3;i++){ for(int j=0;j<3;j++){ cout<<test[i][j]<<" "; } cout<<endl; }
	
	matrix_mult(v,test);
	for(int i=0;i<3;i++){ cout<<v[i]<<" "; } cout<<endl;
}

ll result_count(vector<vector<ll> > &a){
	ll final_ans = 0;	
	for(int i=1;i<ukuran;i++){
		ll P=1, tmpf;
		for(int j=1;j<ukuran;j++){
			tmpf = mulmod(combin[i_prima[j]][i_matrix[i][j]] , fast_exp(j,i_matrix[i][j],MODULO) , MODULO);
			P = mulmod(P,tmpf,MODULO);
		}
		
		for(int j=1;j<ukuran;j++){
			final_ans = (final_ans+(P*a[i][j]))%MODULO;
		}
	}
	return final_ans%MODULO;
}

int main(){
	TESTCASES = false;
	DEBUG = false;
	
	
	sieve();
	ll n,m,l=1;
	
	if (TESTCASES) {
		//unit_test();
		cin>>l; 
	}
	
	while(l--){	
		cin>>n>>m;
		if (m<2){
			cout<<"1\n";
		} else {
			start_factorize(m);
			calculate_final_v3(n);
			
			
			if (n==1){
				ll final_ans=1;
				for (int i=1;i<pow_size;i++){
					final_ans = (final_ans*fast_exp(i+1,i_prima[i],MODULO));
				}
				cout<<final_ans<<endl;
			} else {
				prepare_combin();
				
				if (DEBUG){
					cout<<"t_matrix:"<<endl;
					for(int i=0;i<t_matrix.size();i++){
						for(int j=0;j<t_matrix.size();j++){
							cout<<t_matrix[i][j]<<" ";
						} cout<<endl;
					}
				}
						
				matrix_exp(t_matrix, n-2);	
				
				if (DEBUG){
					cout<<"t_matrix:"<<endl;
					for(int i=0;i<t_matrix.size();i++){
						for(int j=0;j<t_matrix.size();j++){
							cout<<t_matrix[i][j]<<" ";
						} cout<<endl;
					}
				}
							
				ll final_ans =result_count(t_matrix);
				cout<<final_ans<<endl;
			}
		}
	}
	
	return 0;
}
