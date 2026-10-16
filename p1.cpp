#include <bits/stdc++.h>
#include <atcoder/all>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

#ifdef DEBUG
#include <icecream.hpp>
#else
#define IC(...) {}
#endif

using namespace std;
using namespace atcoder;
using namespace __gnu_pbds;

// ==================================================
// Basic aliases / constants
// ==================================================
using ll = long long;
using mint = modint998244353;
using Graph = vector<vector<ll>>;
using Edge = pair<int, ll>; // {to, weight}

constexpr ll MOD = 998244353LL;
// constexpr ll MOD = 1000000007LL;
//constexpr ll INF = (1LL << 60);
constexpr ll INF = numeric_limits<ll>::max() / 2;

#define rep(i, n) for (ll i = 0; i < (ll)(n); i++)
#define rep1(i, n) for (ll i = 1; i <= (ll)(n); i++)
#define rep3(i, s, n) for (ll i = (s); i <= (ll)(n); i++)
#define ALL(x) (x).begin(), (x).end()
#define RALL(x) (x).rbegin(), (x).rend()
#define bit(v, n) ((v >> n) & 1)

// よく使うグリッド用の4近傍。方向文字は添字をDR/DCと揃える。
const int DR[] = {0, 1, 0, -1};
const int DC[] = {1, 0, -1, 0};
const char DIREC[] = "RDLU";

// 競プロ中に雑に使うグローバル変数。必要ならsolve内のローカルに移す。
int N, M;
int H, W;

template <class T>
inline bool chmin(T& a, const T& b) {
    if (a <= b) return false;
    a = b;
    return true;
}

template <class T>
inline bool chmax(T& a, const T& b) {
    if (a >= b) return false;
    a = b;
    return true;
}

// ==================================================
// Graph algorithms
// ==================================================
void dijkstra(int start, const vector<vector<Edge>>& graph, vector<ll>& dist) {
    int n = (int)graph.size();
    dist.assign(n, INF);
    dist[start] = 0;

    using State = pair<ll, int>; // {distance, vertex}
    priority_queue<State, vector<State>, greater<State>> pq;
    pq.push({0, start});

    while (!pq.empty()) {
        auto [d, v] = pq.top();
        pq.pop();
        if (d != dist[v]) continue;

        for (auto [to, w] : graph[v]) {
            if (chmin(dist[to], dist[v] + w)) {
                pq.push({dist[to], to});
            }
        }
    }
}

// 複数の始点から同時に最短距離を求める。全始点の距離は0。
void multi_start_dijkstra(const vector<int>& starts,
                          const vector<vector<Edge>>& graph,
                          vector<ll>& dist) {
    int n = (int)graph.size();
    dist.assign(n, INF);

    using State = pair<ll, int>;
    priority_queue<State, vector<State>, greater<State>> pq;

    for (int s : starts) {
        dist[s] = 0;
        pq.push({0, s});
    }

    while (!pq.empty()) {
        auto [d, v] = pq.top();
        pq.pop();
        if (d != dist[v]) continue;

        for (auto [to, w] : graph[v]) {
            if (chmin(dist[to], dist[v] + w)) {
                pq.push({dist[to], to});
            }
        }
    }
}

// 辺重みが0または1だけの最短路。通常のDijkstraより軽い。
void zero_one_bfs(int start, const vector<vector<Edge>>& graph, vector<ll>& dist) {
    int n = (int)graph.size();
    dist.assign(n, INF);
    dist[start] = 0;

    deque<int> dq;
    dq.push_back(start);

    while (!dq.empty()) {
        int v = dq.front();
        dq.pop_front();

        for (auto [to, w] : graph[v]) {
            if (chmin(dist[to], dist[v] + w)) {
                if (w == 0) dq.push_front(to);
                else dq.push_back(to);
            }
        }
    }
}

// 重みを無視した最短手数。graphはEdge型でもtoだけを見る。
void bfs(int start, const vector<vector<Edge>>& graph, vector<int>& dist) {
    int n = (int)graph.size();
    dist.assign(n, INT_MAX);
    dist[start] = 0;

    queue<int> q;
    q.push(start);

    while (!q.empty()) {
        int v = q.front();
        q.pop();
        for (auto [to, _] : graph[v]) {
            if (dist[to] != INT_MAX) continue;
            dist[to] = dist[v] + 1;
            q.push(to);
        }
    }
}

// 全点対最短路。dist[i][i]=0、辺dist[u][v]=wで初期化してから呼ぶ。
void warshall_floyd(vector<vector<ll>>& dist) {
    int n = (int)dist.size();
    for (int k = 0; k < n; k++) {
        for (int i = 0; i < n; i++) {
            if (dist[i][k] == INF) continue;
            for (int j = 0; j < n; j++) {
                if (dist[k][j] == INF) continue;
                chmin(dist[i][j], dist[i][k] + dist[k][j]);
            }
        }
    }
}

// 負辺あり単一始点最短路。負閉路があるとfalseを返す。
bool bellman_ford(int start, const vector<vector<Edge>>& graph, vector<ll>& dist) {
    int n = (int)graph.size();
    dist.assign(n, INF);
    dist[start] = 0;

    for (int iter = 0; iter < n - 1; iter++) {
        bool updated = false;
        for (int v = 0; v < n; v++) {
            if (dist[v] == INF) continue;
            for (auto [to, w] : graph[v]) {
                updated |= chmin(dist[to], dist[v] + w);
            }
        }
        if (!updated) break;
    }

    for (int v = 0; v < n; v++) {
        if (dist[v] == INF) continue;
        for (auto [to, w] : graph[v]) {
            if (dist[v] + w < dist[to]) return false;
        }
    }
    return true;
}

// DAGのトポロジカル順序を返す。閉路がある場合、返る頂点数がn未満になる。
vector<int> topological_sort(const vector<vector<int>>& g) {
    int n = (int)g.size();
    vector<int> indeg(n), order;
    for (int v = 0; v < n; v++) {
        for (int to : g[v]) indeg[to]++;
    }

    queue<int> q;
    for (int v = 0; v < n; v++) {
        if (indeg[v] == 0) q.push(v);
    }

    while (!q.empty()) {
        int v = q.front();
        q.pop();
        order.push_back(v);
        for (int to : g[v]) {
            if (--indeg[to] == 0) q.push(to);
        }
    }
    return order;
}

// 有向グラフのサイクル検出。無向グラフなら親への逆辺を除外する。
bool dfs_cyc(const Graph& g, int v, vector<bool>& seen, vector<bool>& finished) {
    seen[v] = true;
    for (ll to : g[v]) {
        if (finished[to]) continue;
        if (seen[to]) return true;
        if (dfs_cyc(g, (int)to, seen, finished)) return true;
    }
    finished[v] = true;
    return false;
}

// ==================================================
// Number theory / combinatorics
// ==================================================
ll gcd(ll a, ll b) {
    if (b == 0) return abs(a);
    return gcd(b, a % b);
}

ll mod_pow(ll x, ll y, ll mod = MOD) {
    ll res = 1 % mod;
    x %= mod;
    while (y > 0) {
        if (y & 1) res = res * x % mod;
        x = x * x % mod;
        y >>= 1;
    }
    return res;
}

// gcd(a,m)=1のとき、mod mでのaの逆元を返す。
ll modinv(ll a, ll m) {
    ll b = m, u = 1, v = 0;
    while (b) {
        ll t = a / b;
        a -= t * b;
        swap(a, b);
        u -= t * v;
        swap(u, v);
    }
    u %= m;
    if (u < 0) u += m;
    return u;
}

// 有理数復元。mod上の値xから、小さい分子/分母 r/t を推定する。
pair<ll, ll> rational_reconstruction(ll x, ll mod) {
    ll r0 = mod, r1 = x;
    ll t0 = 0, t1 = 1;

    while (r1 * r1 > mod) {
        ll q = r0 / r1;
        tie(r0, r1) = make_pair(r1, r0 - q * r1);
        tie(t0, t1) = make_pair(t1, t0 - q * t1);
    }
    return {r1, t1};
}

constexpr int COMB_MAX = 1000000;
vector<ll> fact(COMB_MAX + 1), inv_fact(COMB_MAX + 1);

// nCkをO(1)で使うための前計算。MODは素数前提。
void init_comb() {
    fact[0] = 1;
    for (int i = 1; i <= COMB_MAX; i++) {
        fact[i] = fact[i - 1] * i % MOD;
    }

    inv_fact[COMB_MAX] = mod_pow(fact[COMB_MAX], MOD - 2);
    for (int i = COMB_MAX - 1; i >= 0; i--) {
        inv_fact[i] = inv_fact[i + 1] * (i + 1) % MOD;
    }
}

ll comb(int n, int k) {
    if (n < 0 || k < 0 || n < k) return 0;
    return fact[n] * inv_fact[k] % MOD * inv_fact[n - k] % MOD;
}

// 試し割り素因数分解。nが大きくクエリが多いならspf版を使う。
vector<pair<ll, ll>> pf_slow(ll n) {
    vector<pair<ll, ll>> res;
    for (ll p = 2; p * p <= n; p++) {
        if (n % p != 0) continue;
        ll cnt = 0;
        while (n % p == 0) {
            n /= p;
            cnt++;
        }
        res.push_back({p, cnt});
    }
    if (n > 1) res.push_back({n, 1});
    return res;
}

vector<char> sieve_char(int n) {
    vector<char> is_prime(n + 1, true);
    if (n >= 0) is_prime[0] = false;
    if (n >= 1) is_prime[1] = false;

    for (int p = 2; p * p <= n; p++) {
        if (!is_prime[p]) continue;
        for (ll x = 1LL * p * p; x <= n; x += p) {
            is_prime[x] = false;
        }
    }
    return is_prime;
}

constexpr int SPF_MAX = 10000000;
vector<int> spf(SPF_MAX + 1);

// pf()の前に呼ぶ。n <= SPF_MAXが前提。
void init_spf() {
    iota(ALL(spf), 0);
    for (int p = 2; p * p <= SPF_MAX; p++) {
        if (spf[p] != p) continue;
        for (int x = p * p; x <= SPF_MAX; x += p) {
            if (spf[x] == x) spf[x] = p;
        }
    }
}

vector<pair<ll, ll>> pf(ll n) {
    vector<pair<ll, ll>> res;
    while (n > 1) {
        ll p = spf[n], cnt = 0;
        while (n > 1 && spf[n] == p) {
            n /= p;
            cnt++;
        }
        res.push_back({p, cnt});
    }
    return res;
}

// ==================================================
// Data structures
// ==================================================
// Trie: 文字列集合。insert/search/removeを提供する。
struct Trie {
    struct Node {
        map<char, int> next;
        bool is_end = false;
    };

    vector<Node> nodes;

    Trie() : nodes(1) {}

    void insert(const string& s) {
        int cur = 0;
        for (char c : s) {
            if (!nodes[cur].next.count(c)) {
                nodes[cur].next[c] = (int)nodes.size();
                nodes.push_back(Node());
            }
            cur = nodes[cur].next[c];
        }
        nodes[cur].is_end = true;
    }

    bool search(const string& s) const {
        int cur = 0;
        for (char c : s) {
            auto it = nodes[cur].next.find(c);
            if (it == nodes[cur].next.end()) return false;
            cur = it->second;
        }
        return nodes[cur].is_end;
    }

    bool remove(const string& s) {
        int cur = 0;
        for (char c : s) {
            auto it = nodes[cur].next.find(c);
            if (it == nodes[cur].next.end()) return false;
            cur = it->second;
        }
        if (!nodes[cur].is_end) return false;
        nodes[cur].is_end = false;
        return true;
    }
};

// order_of_key(x): x未満の個数、find_by_order(k): 0-indexedでk番目。
using ordered_set = tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update>;

// 重複を扱いたいときは {値, 挿入ID} を入れる。
using ordered_multiset = tree<pair<int, int>, null_type, less<pair<int, int>>, rb_tree_tag, tree_order_statistics_node_update>;

// 重み付きUnion-Find。
// unite(x, y, w): weight(y) - weight(x) = w を追加する。
struct WeightedUF {
    int n;
    vector<int> parent, rank;
    vector<ll> diff; // diff[x] = weight(x) - weight(parent[x])

    WeightedUF(int n) : n(n), parent(n), rank(n, 0), diff(n, 0) {
        iota(ALL(parent), 0);
    }

    int find(int x) {
        if (parent[x] == x) return x;
        int r = find(parent[x]);
        diff[x] += diff[parent[x]];
        return parent[x] = r;
    }

    ll weight(int x) {
        find(x);
        return diff[x];
    }

    bool unite(int x, int y, ll w) {
        w += weight(x);
        w -= weight(y);
        x = find(x);
        y = find(y);
        if (x == y) return w == 0;

        if (rank[x] < rank[y]) {
            swap(x, y);
            w = -w;
        }
        if (rank[x] == rank[y]) rank[x]++;
        parent[y] = x;
        diff[y] = w;
        return true;
    }

    bool same(int x, int y) {
        return find(x) == find(y);
    }

    ll diff_weight(int x, int y) {
        return weight(y) - weight(x);
    }
};

// Parity Union-Find。
// unite(x, y, 0): 同色、unite(x, y, 1): 異色。矛盾するとfalse。
struct ParityUF {
    int n;
    vector<int> parent, rank, parity;

    ParityUF(int n) : n(n), parent(n), rank(n, 0), parity(n, 0) {
        iota(ALL(parent), 0);
    }

    int find(int x) {
        if (parent[x] == x) return x;
        int r = find(parent[x]);
        parity[x] ^= parity[parent[x]];
        return parent[x] = r;
    }

    int color(int x) {
        find(x);
        return parity[x];
    }

    bool unite(int x, int y, int w) {
        w ^= color(x);
        w ^= color(y);
        x = find(x);
        y = find(y);
        if (x == y) return w == 0;

        if (rank[x] < rank[y]) swap(x, y);
        parent[y] = x;
        parity[y] = w;
        if (rank[x] == rank[y]) rank[x]++;
        return true;
    }

    bool same(int x, int y) {
        return find(x) == find(y);
    }

    int diff(int x, int y) {
        return color(x) ^ color(y);
    }
};

// Cartesian Tree。inorderが元配列順、親が子以下になるmin-heapを作る。
struct CartesianTree {
    vector<int> parent, left, right;

    CartesianTree(const vector<ll>& a) {
        int n = (int)a.size();
        parent.assign(n, -1);
        left.assign(n, -1);
        right.assign(n, -1);

        stack<int> st;
        for (int i = 0; i < n; i++) {
            int last = -1;
            while (!st.empty() && a[st.top()] > a[i]) {
                // max-heapにしたい場合は比較を a[st.top()] < a[i] に変える。
                last = st.top();
                st.pop();
            }
            if (!st.empty()) {
                right[st.top()] = i;
                parent[i] = st.top();
            }
            if (last != -1) {
                left[i] = last;
                parent[last] = i;
            }
            st.push(i);
        }
    }
};

// ==================================================
// Grid helpers
// ==================================================
#define RC(r, c) ((r) * N + (c))
#define R(rc) ((rc) / N)
#define C(rc) ((rc) % N)

bool inside_square(int r, int c) {
    return 0 <= r && r < N && 0 <= c && c < N;
}

inline bool inside(int r, int c, int h, int w) {
    return 0 <= r && r < h && 0 <= c && c < w;
}

template <class T>
class Grid {
public:
    int H = 0, W = 0, HW = 0;
    vector<T> grid;

    Grid() = default;

    explicit Grid(int n) : H(n), W(n), HW(n * n), grid(HW, T()) {}

    Grid(int h, int w) : H(h), W(w), HW(h * w), grid(HW, T()) {}

    void fill(const T& v) {
        std::fill(ALL(grid), v);
    }

    void read() {
        for (int r = 0; r < H; r++) {
            for (int c = 0; c < W; c++) cin >> at(r, c);
        }
    }

    bool inside(int r, int c) const {
        return 0 <= r && r < H && 0 <= c && c < W;
    }

    T& operator()(int r, int c) {
        return grid[r * W + c];
    }

    const T& operator()(int r, int c) const {
        return grid[r * W + c];
    }

    T& at(int rc) {
        assert(0 <= rc && rc < HW);
        return grid[rc];
    }

    const T& at(int rc) const {
        assert(0 <= rc && rc < HW);
        return grid[rc];
    }

    T& at(int r, int c) {
        assert(inside(r, c));
        return grid[r * W + c];
    }

    const T& at(int r, int c) const {
        assert(inside(r, c));
        return grid[r * W + c];
    }

    void show() const {
        for (int r = 0; r < H; r++) {
            for (int c = 0; c < W; c++) cerr << at(r, c);
            cerr << '\n';
        }
    }

    void show2(int width = 3) const {
        for (int r = 0; r < H; r++) {
            for (int c = 0; c < W; c++) cerr << setw(width) << at(r, c);
            cerr << '\n';
        }
    }
};

// ==================================================
// Sequence / geometry helpers
// ==================================================
// bは0..b.size()-1に座圧済みの値。
ll inversion(const vector<ll>& b) {
    ll ans = 0;
    fenwick_tree<ll> fw(b.size());
    rep(i, (ll)b.size()) {
        ans += i - fw.sum(0, b[i]);
        fw.add(b[i], 1);
    }
    return ans;
}

template <class T>
vector<pair<T, ll>> run_length(const vector<T>& a) {
    vector<pair<T, ll>> res;
    if (a.empty()) return res;

    T cur = a[0];
    ll cnt = 1;
    for (size_t i = 1; i < a.size(); i++) {
        if (a[i] == cur) {
            cnt++;
        } else {
            res.push_back({cur, cnt});
            cur = a[i];
            cnt = 1;
        }
    }
    res.push_back({cur, cnt});
    return res;
}

// vを書き換えて座圧後の値にし、元の値一覧xsを返す。
template <class T>
vector<T> compress(vector<T>& v) {
    vector<T> xs = v;
    sort(ALL(xs));
    xs.erase(unique(ALL(xs)), xs.end());
    for (auto& x : v) {
        x = lower_bound(ALL(xs), x) - xs.begin();
    }
    return xs;
}

struct Vec {
    ll x, y;
};

inline bool upper(const Vec& a) {
    return (a.y > 0) || (a.y == 0 && a.x > 0);
}

inline ll cross(const Vec& a, const Vec& b) {
    return a.x * b.y - a.y * b.x;
}

// 右方向を始点に反時計回りで偏角ソートする比較関数。
bool angle_less(const Vec& a, const Vec& b) {
    bool ua = upper(a), ub = upper(b);
    if (ua != ub) return ua > ub;
    return cross(a, b) > 0;
}

bool same_dir(const Vec& a, const Vec& b) {
    return cross(a, b) == 0 && (a.x * b.x + a.y * b.y) > 0;
}

// ==================================================
// Digit DP skeleton
// ==================================================
/*
string S;
int L;
ll dp[105][2];
bool used[105][2];

ll digit_dp(int pos, bool tight) {
    if (pos == L) {
        // 条件を満たすなら1、満たさないなら0。
        return 1;
    }
    if (!tight && used[pos][0]) return dp[pos][0];

    int limit = tight ? S[pos] - '0' : 9;
    ll res = 0;
    for (int d = 0; d <= limit; d++) {
        bool ntight = tight && (d == limit);
        res += digit_dp(pos + 1, ntight);
    }

    if (!tight) {
        used[pos][0] = true;
        dp[pos][0] = res;
    }
    return res;
}
*/

// ラムダ再帰DFSの型を忘れたとき用。
/*
auto dfs = [&](auto&& self, int v) -> void {
    for (int to : graph[v]) {
        self(self, to);
    }
};
dfs(dfs, start);
*/

// ordered_multisetの典型操作。
/*
ordered_multiset s;
int timer = 0;

s.insert({value, timer++});

auto it = s.lower_bound({value, 0});
if (it != s.end() && it->first == value) s.erase(it);

auto kth = s.find_by_order(k); // 0-indexed
int less_than_x = s.order_of_key({x, -1});
*/

// ==================================================
// Solve
// ==================================================
void solve() {
    // ll N; cin >> N;
    // ll N, M; cin >> N >> M;
    // vector<ll> a(N); rep(i, N) cin >> a[i];
    // ll H, W; cin >> H >> W;
    // vector<string> s(H); rep(i, H) cin >> s[i];
    // ll x, y, z; cin >> x >> y >> z;
    // ll a, b, c; cin >> a >> b >> c;
    // string s; cin >> s;
  
    // ll ans = 0;
    // cout << ans << endl;

    // bool ok = false;
    // cout << (ok ? "Yes" : "No") << endl;
}

int main() {
    //ios::sync_with_stdio(false);
    //cin.tie(nullptr);

    // ll t; cin >> t; while (t--)
    solve();
    return 0;
}
