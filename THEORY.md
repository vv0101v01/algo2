# 理論與演算法：$\mathbb F_7$ 上的仿射代數幾何

本文件給出本庫每個數學結構的**定義、公式、所用定理、由此衍生的演算法**，
以及定理 → 代碼 → 測試的對照。凡是本庫沒有真正實作或無法在 MoonBit
類型系統中成立的主張，都在 §11 明確列為邊界，而不是含糊帶過。

約定：$k=\mathbb F_7$（素數在代碼中是 `pub const PRIME : Int = 7`），
$R=k[x_1,\dots,x_n]$，單項式序為 lex，$x_1>\cdots>x_n$（代碼以 0-based 變量，
index 0 最大，顯示名稱依次為 `x, y, z, w, u, v, s, t`）。
全庫精確算術，**不使用任何浮點數**。

---

## 0. 本庫的兩層世界（先講清楚，否則後面全是假）

有限域上必須分開以下兩層，混為一談是這類項目最常見的造假：

1. **方程層**：理想 $I\lhd R$。商環 $R/I$、Krull 維數、冪零元活在這一層。
   例如 $k[t]/(t^2)$ 中 $\bar t\ne 0,\ \bar t^{\,2}=0$，點集卻只有一個原點。
2. **$\mathbb F_7$-點層**：
   $V_{\mathbb F_7}(I)=\{a\in\mathbb F_7^{\,n}\mid \forall f\in I,\ f(a)=0\}$。
   本層一切有限（每坐標 7 個取值），故列舉是合法且完全的判定程序。

連接兩層的不是教科書原始 Nullstellensatz（那需要代數閉包），而是它的
有限域版本（§6）。反例：$x^2+1$ 在 $\mathbb F_7$ 無根（平方剩餘只有
$0,1,2,4$），故 $V_{\mathbb F_7}((x^2+1))=\varnothing$、
$I(\varnothing)=(1)$，但 $\sqrt{(x^2+1)}=(x^2+1)\ne(1)$。
測試同時斷言這個不一致與修正後的等式。

---

## 1. 地基：域、多項式、除法

### 1.1 定義

- $\mathbb F_7=\mathbb Z/7\mathbb Z$；`Fp::new` 把整數正規化到 $0..6$，
  逆元由 **Fermat 小定理** $a^{-1}=a^{p-2}\,(a\ne0)$ 計算；
  $0$ 的逆元不存在，`try_inv` 返回 `None`，`inv` 則中止——偏函數在 API
  上是顯式的，不假裝全域定義。
- 多項式為稀疏表示：$\sum c_\alpha x^\alpha$，$\alpha\in\mathbb N^n$。
  規範不變量（每個構造函數維護）：項按 lex 嚴格降序、無零係數、單項式不重複。
  因此表示的結構相等 **就是** 多項式相等，無需事後再證。
- 特徵 7 的效應是真檢驗：測試斷言 $(x+y)^7=x^7+y^7$（Freshman's dream）
  與 $2x+5x=0$，整數係數模型會在此翻車。

### 1.2 多元除法（衍生演算法 A1）

`Poly::reduce_by(f, G)`：重複地若某 $\mathrm{LT}(g)\mid\mathrm{LT}(p)$，
以 $p\leftarrow p-\frac{\mathrm{LT}(p)}{\mathrm{LT}(g)}g$ 消去首項，
否則把首項移入餘式。終止性因為 lex 是單項式序（良序且與乘法相容），
首單項式每步嚴格下降。輸出 $r$ 滿足 $f-r\in(G)$ 且 $r$ 無項被任何
$\mathrm{LT}(g)$ 整除。

**關鍵事實**：$G$ 不是 Gröbner 基時餘式不唯一，成員也可留下非零餘式。
反例（測試原樣）：$I=(xy-1,\ y^2-1)$。$y(xy-1)-x(y^2-1)=x-y\in I$，
但以生成元除 $x-y$ 的餘式是 $x-y\ne0$。所以判定理想成員必須先算
Gröbner 基——這不是裝飾性的先後次序，是數學上被迫的。

### 1.3 Buchberger（定理 → 演算法 A2）

- **S-多項式**：$L=\mathrm{lcm}(\mathrm{LM} f,\mathrm{LM} g)$，
  $S(f,g)=\frac{L}{\mathrm{LT} f}f-\frac{L}{\mathrm{LT} g}g$。
- **Buchberger 準則**：$G$ 是 Gröbner 基 ⟺ 每個 $S(g_i,g_j)$ 對 $G$ 約化為 0。
- **演算法**：臨界對隊列；非零約化結果加入基並生成新臨界對。
  終止性 = Dickson 引理 / Hilbert 基定理（首單項式理想升鏈必穩）。
  代碼另設硬步數上限，超限中止而**不**返回一個可能是錯的基
  （`GROEBNER_PAIR_LIMIT`）——「理論上會停」與「資源合約」分開聲明。
- **既約 Gröbner 基唯一性**：首一、極小（首單項式互不整除）、尾部互約化，
  這樣的基唯一。推論是演算法：**理想相等 ⟺ 既約基逐項相等**（可判定）。
  實作中修過一個真 bug：極小化若只向前檢查整除，後加入的較小首項
  （如上例 $x-y$）無法淘汰 $xy-1$，互約化產生零多項式——現為雙向檢查。

---

## 2. 理想演算：公式即演算法

設 $I,J\lhd R$，構造時即算好既約 Gröbner 基（`Ideal::new`），
之後每項判定是一次正規式（normal form）計算 $\mathrm{NF}_I(f)$。

| 運算 | 定義 / 公式 | 演算法 | 幾何對應 |
|---|---|---|---|
| 成員 | $f\in I \iff \mathrm{NF}_I(f)=0$ | Gröbner 約化 | — |
| 和 | $I+J$：生成元並集 | 並集後重算基 | $V(I+J)=V(I)\cap V(J)$ |
| 積 | $IJ$：生成元兩兩乘積 | 同上 | $V(IJ)=V(I)\cup V(J)$ |
| 交 | $I\cap J=\big(tI+(1-t)J\big)\cap k[x]$ | 標籤變量 $t$（最大）lex 消元，取不含 $t$ 的基元 | $V(I\cap J)=V(I)\cup V(J)$ |
| 飽和 | $(I:f^\infty)=\{g\mid \exists k,\ f^kg\in I\}=\big(I+(1-tf)\big)\cap k[x]$ | Rabinowitsch 消元 | 限制到主開集 $D(f)$ |
| 根 | $f\in\sqrt I \iff (I:f^\infty)=(1)$ | 飽和 + 單位理想判定 | $f$ 在 $V_{\bar k}(I)$ 上消沒 |
| 相等 | $I=J$ ⟺ 既約基相同 | 逐項比較 | — |

測試包含精確恆等式，如 $(x)\cap(y)=(xy)$（UFD 中互素）、
互素（comaximal）時 $I\cap J=IJ$（CRT 假設）、一般情形
$(x,y)^2\ne(x,y)=(x,y)\cap(x,y)$ 顯示積與交真會分開。

### 階梯與維數（定理 → 演算法 A3、A4）

- **標準單項式**：不被任何 $\mathrm{LM}(g),g\in\mathrm{GB}(I)$ 整除的單項式。
  它們構成 $R/I$ 作為 $k$-向量空間的一組基（Macaulay）。
  有限性 ⟺ 每個變量有純冪 $x_i^{b_i}$ 成為首單項式；
  此時在盒子 $\prod[0,b_i)$ 內列舉篩選，得 $\dim_k R/I$。
  若無窮維，返回 `None`——不存在的有限模型絕不偽造。
- **Krull 維數**：$\dim R/I=\dim R/\mathrm{in}(I)$（Gröbner 退化保維），而
  $\dim R/M=\max\{|U|: U\subseteq\{x_i\},\ M\cap k[U]=(0)\}$：
  即沒有首單項式的支集完全落在 $U$ 內。轉化為超圖獨立集，對子集枚舉
  （文件明言適用 $n$ 小的精確計算）。單位理想 $\mapsto -1$（空簇）。
  測試：$\mathbb A^2\!:\!2$、拋物線 $/ $扭立方曲線 $(y-x^2,z-x^3)\!:\!1$、
  點 $(x,y)\!:\!0$、「肥點」 $(x^2,xy,y^2)$：$\dim_k=3$，Krull 維數 0。

---

## 3. 商環 $R/I$

**定義**：陪集 $f+I$，加乘由代表元定義。**表示定理**：
$\mathrm{NF}_I(f)$ 是陪集的唯一正規代表元；運算 = 代表元運算後取 NF。
良定性是測試命題而非口號：隨機把代表元改成 $f+\sum h_i g_i$，
所有陪集運算結果必須不變；且 $\ker(R\to R/I)=I$ 兩向隨機檢驗。

**普遍性質（代碼 `QuotientRing::evaluate`）**：多項式環的普遍性質說
變量像任意指定即唯一擴張成 $R\to S$ 的同態；它下降到 $R/I$
⟺ $I$ 的生成元在 $S$ 中取值為 0。商的普遍性質由此得到。

**第一同構定理（衍生驗證）**：在有限維情形，階梯基給出結構常數模型
（§5），求值映射 $R/I(X)\to \mathrm{Func}(X,k)$ 在 §6 被驗證為同構。

類型事實：`Coset` 與 `Poly` 是不同類型，原多項式不經商映射
`of_poly` 無法當陪集用。但理想 $I$ 是運行時數據，MoonBit 無依賴類型，
故「哪個商」以運行時結構標籤守衛，混用即中止——這是明寫的邊界，
不偽裝成編譯期索引（§11）。

---

## 4. 直積、乘積（環層與類型層）

### 4.1 環的直積 $A\times B$

逐分量運算；有限代數上是**塊對角結構常數**，$\dim=\dim A+\dim B$。
普遍性質：$\mathrm{Hom}(C,A\times B)\cong\mathrm{Hom}(C,A)\times\mathrm{Hom}(C,B)$；
配對 $\langle\varphi,\psi\rangle$ 是座標堆疊。測試以矩陣等式驗證三角律
$\pi_A\circ\langle\varphi,\psi\rangle=\varphi$，並含負對照：
$t\mapsto(1,2)$ 不是 $k[t]/(t^2-1)\to k^2$ 的同態（$2^2\ne1$），
`verify` 必須拒絕。正交冪等元 $(1,0),(0,1)$ 分解 $1$——不交並
坐標環分解背後正是這件事（§7）。

### 4.2 中國剩餘定理（推論算法）

$m_p,m_q$ 互素 ⇒
$R/(m_p\cap m_q)\;\xrightarrow{\sim}\;R/m_p\times R/m_q\cong k\times k$，
映射是兩點求值；逆映射有顯式公式，如在 $(0,0),(1,0)$ 處取
$(a,b)$ 的多項式 $a(1-x)+bx$。測試對全部 $7\times7$ 數值驗證逆公式，
並驗證 CRT 映射是結構常數意義下的同構（同態檢驗 + 矩陣可逆）。

### 4.3 類型層乘積 `Prod[A,B]`（`category.mbt`）

`pairing(f,g) : X → Prod[A,B]` 具現乘積普遍性質；投影 `.fst/.snd`
是結構的一部份；`prod_map` 是雙函子性。映射**進入**乘積
$= $ 一對映射——在環層、簇層、類型層是同一個形狀（§7 簇乘積的
`pair_poly_maps`、§4.1 環配對），三處各自實作、各自驗證。

---

## 5. 有限維 $k$-代數（結構常數）與張量積

### 5.1 模型

代數 $A=(d,\ (c_{ij}^k),\ 1\text{ 的坐標})$，
$e_ie_j=\sum_k c_{ij}^k e_k$，元素是坐標向量，乘法是常數收縮。
`check_axioms` 在基底元上全檢交換、結合、單位（分配律由雙線性延拓
自動成立，另有一般元素的隨機環公理測試）。
同態 = 矩陣；**是同態與否是被判定而非宣稱**：`AlgHom::verify` 檢查
$1\mapsto1$ 與全部 $d^2$ 個基底乘積
（線性是矩陣自帶的，故此檢驗完備——這是該斷言的證明綱要）。
`is_isomorphism` 再要求矩陣可逆且逆矩陣也通過同態檢驗。
元素是否可逆元由精確線性求解 $m_x(y)=1$ 判定（`mult_matrix` + `solve`）。

零環邊界按普遍性質處理：零環是終對象，入零環的同態唯一存在；
出零環入非零環不存在；兩者均有測試。

### 5.2 張量積 $A\otimes_k B$

基底 $e_i\otimes f_j$，常數是 Kronecker 積
$(c^{A\otimes B})_{(i,j)(i',j')}^{(i'',j'')}=c^A_{ii'}{}^{i''}c^B_{jj'}{}^{j''}$，
$\dim A\otimes B=\dim A\cdot\dim B$（坐標為矩陣，純張量 $x\otimes y$
是外積，故表示正規、無需再冒商去「雙線性關係」，關係轉而被測試驗證：
$(x_1+x_2)\otimes y$、$(cx)\otimes y=x\otimes(cy)$、
$(x\otimes y)(x'\otimes y')=xx'\otimes yy'$）。

- **向量空間普遍性質**：雙線性映射 $A\times B\to C$ ⟺ 線性映射
  $A\otimes B\to C$。測試實例：
  $\delta_i,\delta_j\mapsto\delta_{(i,j)}$ 提升出同構
  $k^2\otimes k^3\cong k^6$（被 `is_isomorphism` 檢驗）。
- **代數餘積普遍性質**：$\varphi:A\to C,\ \psi:B\to C$ 唯一誘導
  $A\otimes B\to C$，$e_i\otimes f_j\mapsto\varphi(e_i)\psi(f_j)$
  （$C$ 交換使兩像交換）（`tensor_copair_hom`，三角律以矩陣等式測試）。
- **多項式商的張量積**（定理）：
  $k[x]/I\ \otimes_k\ k[y]/J\ \cong\ k[x,y]/(I+J)$。
  測試取 $A=k[x]/(x^2-2)$、$B=k[y]/(y^2+y+1)$，
  以階梯基 $x^i\otimes y^j\mapsto \overline{x^iy^j}$ 為候選映射，
  與直接建的二元商模型之間驗證同構；把基像打亂作為同態必須被拒。

### 5.3 有限代數的商（定理 → 演算法）

給子空間（以基給出）：先判定是否理想（用每個基元乘遍代數基底仍在子空間），
**不是理想便中止，不產生假商**。若是：貪心由標準基取補空間，
陪集乘法 = 提升、乘、沿補投影。核被測試為恰是該理想，
誘導映射 = 第一同構定理的形狀（如
$k^3/(\delta_0)\cong k^2$ 的限制映射被驗證為同構）。

---

## 6. 仿射簇與坐標環

### 6.1 定義

- $\mathbb A^n_{\mathbb F_7}$ 點列舉（$7^n$ 點，字典序正規序）；
  $V(I)=\{a\mid \forall g\in\text{生成元},\, g(a)=0\}$；
  $m_a=(x_1-a_1,\dots,x_n-a_n)=\ker(\mathrm{ev}_a)$；
  點集 $X$ 的消失理想 $I(X)=\bigcap_{a\in X}m_a$，
  由理想交逐點算出（$I(\varnothing)=(1)$）。
- **Zariski 演算**：
  $V(I+J)=V(I)\cap V(J)$、$V(I\cap J)=V(I)\cup V(J)=V(IJ)$、
  $I\subseteq J\Rightarrow V(J)\subseteq V(I)$（Galois 連結），
  皆對全部 49 個 $\mathbb A^2$ 點逐點測試，不是抽樣口號。

### 6.2 有限域 Nullstellensatz（定理 → 双獨立算法一致性）

$$ I\big(V_{\mathbb F_7}(I)\big)=\sqrt{\,I+\mathfrak F\,}, \qquad
\mathfrak F=(x_1^7-x_1,\dots,x_n^7-x_n). $$

理由綱要：在代數閉包中 $\mathfrak F$ 的零點恰為 $\mathbb F_7^n$，
故閉包上對 $I+\mathfrak F$ 用 Hilbert Nullstellensatz，再由域擴張下
理想成員關係的收縮回到基域。測試比較兩條**獨立**判定路線在隨機 $f$
上完全一致：點列舉（$f$ 是否在全部點消沒）vs 飽和（$f\in\sqrt{I+\mathfrak F}$），
且樣本保證雙向都出現。場方程這一修正就是整層幾何能精確成立的原因。

### 6.3 坐標環 $k[X]$

**定義**：$k[X]:=k[x]/I(X)$。本庫以函數表實現它：元素是
$X\to k$ 的數值表，$\delta_a$ 基底逐點乘法。識別的證明是可運算的：

- **指示多項式** $\delta_a(x)=\prod_i\big(1-(x_i-a_i)^{p-1}\big)$：
  由 Fermat 小定理，它在 $a$ 取 1、在其餘一切 $\mathbb F_7$ 點取 0。
- **插值**：任意表 $(v_a)$ 等於 $\sum v_a\delta_a$ 的表——即求值映射
  $k[x]\to\mathrm{Func}(X,k)$ 滿射；核是 $I(X)$ 由構造顯然。
- 於是 $k[X]\cong\prod_{a\in X} k$（CRT 的形式），$\dim_k k[X]=|X|$。
  測試在商的階梯模型與函數代數之間把求值映射驗證為同構
  （第一同構定理的完整可檢形式），並驗證不同點極大理想兩兩互素。

坐標環（函數表）與方程商 $k[x]/I$ 的區別是實質的：
$I$ 非 $\mathbb F_7$-根時後者能含冪零元等非既約/非點層訊息，
前者恆既約且維數 $=|V_{\mathbb F_7}(I)|$。兩者在本庫是不同類型/函數
（`QuotientRing` vs `CoordRing`），不能互換充數。

點數例子（真列舉）：$y=x^2$ 7 點；圓 $x^2+y^2=1$ 在 $\mathbb F_7$ 有 8 點
（含 $(\pm2,\pm2)$，因 $4+4=8=1$），歐氏直覺會給錯答案。

---

## 7. 簇的乘積與不交並；反變函子把兩者互換角色

### 7.1 乘積簇 $X\times Y\subseteq\mathbb A^{n+m}$

定義方程：$X$ 的方程寫在前 $n$ 變量、$Y$ 的寫在後 $m$ 變量
（理想在 $k[x,y]$ 中的和）。點自動是笛卡兒積（方程塊獨立），
測試與直接笛卡兒列舉對照。投影是多項式映射；
普遍性質由 `pair_poly_maps`（分量串接）提供，投影 ∘ 配對
在**多項式相等**層面回復原映射（比分點相等更強）。

**定理** $k[X\times Y]\cong k[X]\otimes_k k[Y]$：
$\delta_a\otimes\delta_b\mapsto\delta_{(a,b)}$。測試驗證它為同構。
幾何的乘積變成代數的**餘積**（張量積）——這是下述對偶的核心內容，
不是巧合命名。

### 7.2 不交並 $X\sqcup Y$

標準標籤嵌入 $\mathbb A^{n+m+1}$：
$x\mapsto(x,0,0)$、$y\mapsto(0,y,1)$；
定義理想接著**算出來**——即標籤點集的消失理想（極大理想交），
故結果是具顯式方程的閉子集，不僅是一張清單。
兩像由標籤坐標分離，即便底點相同（如 $-1$ 同屬兩邊）也不相撞。

**定理** $k[X\sqcup Y]\cong k[X]\times k[Y]$（直積）：
標籤為 0 的 $\delta$ 送到 $(\delta,0)$，為 1 的送到 $(0,\delta)$，
被驗證為同構。餘普遍性質的具體實例也在測試中：
$[\text{左取常值 }2,\ \text{右取恆等}]$ 被實現為單一多項式
$\varphi=2(1-t)+y\,t$ 在標籤坐標中逐點核實。
（類型層的同一條普遍性質是 `Sum::sum_elim`，窮盡性由編譯器檢查；
分配律 $A\times(B+C)\cong AB+AC$ 在類型層是正則雙射，
其幾何類似只有經上述對偶才成立，兩層不混稱。）

---

## 8. 態射與反變性（Contravariance）

**多項式映射** $F:\mathbb A^n\to\mathbb A^m$ 以分量多項式給出。
**拉回** $F^\*(f)=f\circ F$ 把方向反轉：
$\mathrm{AffVar}^{\mathrm{op}}\to k\text{-Alg}$，$X\mapsto k[X]$。

**函子律（定理）**：$\mathrm{id}^\*=\mathrm{id}$，
$(g\circ f)^\* = f^\*\circ g^\*$——次序反轉。
測試在三個層面各驗證一次：多項式（作文法上的覆合）、
函數表（$f^\*(\phi)(a)=\phi(f(a))$）、坐標環同態矩陣
（`pullback_hom(f).compose(pullback_hom(g))` 與直接拉回逐元相等），
且態射性本身可判定（$X$ 每點像落入 $Y$；含「投影不落入 $\{1,-1\}$」
這類負對照）。

**Spec 方向（有限反等價）**：有限點簇與有限個 $k$ 的直積之間，
`induced_point_map` 由同態 $\varphi:k[Y]\to k[X]$ 追蹤本原冪等元
$\varphi(\delta_b)(a)\in\{0,1\}$ 回復出點映射 $X\to Y$（理由：直積域間的
同態由指標集上的函數決定）。兩向往返（點映射→拉回→回復；
抽象點指派→同態→回復→插值成多項式映射→拉回矩陣相同）都有測試——
這是仿射簇 ⇄ 有限生成既約代數反等價在**有限點**情形下的完整版本，
明言其範圍，不冒充一般情形的構造。

---

## 9. 局部化 Localization

### 9.1 商環沿 $\{f^k\}$ 的局部化 $S^{-1}(R/I)$

分數 $a/f^k$。**正確（非整環亦適用）的等式關係**：
$$ \frac{a}{f^i}=\frac{b}{f^j}
\iff \exists k:\ f^k\big(f^{\,j}a-f^{\,i}b\big)\in I
\iff f^{\,j}a-f^{\,i}b\in (I:f^\infty). $$
飽和 $(I:f^\infty)$ 構造時由 Gröbner 消元算定一次，等式判定是一次
成員檢驗。單用叉乘而去掉存在因子 $f^k$ 對零因子會出錯——測試主例：
$R=k[x,y]/(xy)$、$S=\{x^k\}$：$(xy:x^\infty)=(y)$，故 $y/1=0$
（而在 $R$ 中 $y\ne0$），且 $y$ 的一切倍式都死；
核 $\ker\big(R/I\to S^{-1}(R/I)\big)=(I:f^\infty)/I$ 兩向樣本驗證。
整環情形是推論：多項式環裡 $(0:f^\infty)=(0)$，等式退化成普通叉乘
（被斷言而非另寫一套分數）。

**退化判定**：局部化為零環 ⟺ $(I:f^\infty)=(1)$
⟺ $f$ 模 $I$ 冪零。幾何上 $D(f)\cap V(I)=\varnothing$。
$k[t]/(t^2)$ 沿 $t$ 是主例（$1=0$ 被斷言，而不是讓它默默壞掉）。

### 9.2 Rabinowitsch 同構（定理 → 雙向映射）

$$ S^{-1}(R/I)\ \cong\ R[t]\big/\big(I,\ tf-1\big),\qquad
a/f^k\mapsto a t^k,\quad [g(x,t)]\mapsto g(x,1/f). $$

兩向都實作（`RabinowitschIso::forward/backward`）：正向保加、乘，
尊重分數擴分；往返合成在兩邊各是恆等（商的陪集相等 / 分數等式）。
幾何面孔是 §6 的 `principal_open_as_variety`：主開集
$D(f)\cap X$ 成為 $\mathbb A^{n+1}$ 中閉圖 $tf=1$，$t$-坐標 $=1/f(a)$
逐點核實；$|D(x)\cap\mathbb A^1|=6$ 如此類推。

### 9.3 一點處局部環 $\mathcal O_{\mathbb A^n,a}$

$S=k[x]\setminus m_a$（不是主型乘法集，故為獨立類型）：
$a/s$，要求 $s(a)\ne0$，由返回 `Option` 的構造函數強制。
剩餘域映射 $a/s\mapsto a(a)/s(a)$；唯一極大理想
$\mathfrak m=\{a/s\mid a(a)=0\}$ = 非可逆元集合。
測試（隨機分數）：剩餘映射同態、核 $\!=\!\mathfrak m$、可逆 ⟺ 不在 $\mathfrak m$、
$\mathfrak m$ 對加法與乘任意元封閉（局部環性質）、逆元實際相乘為 1。
由於底環是整環，此處等式由叉乘判定合法，註明依賴整域性質；
$f^k$ 型的一般商局部化則用 §9.1 的飽和等式，兩者不混用。

### 9.4 有限代數的局部化（特有定理 → 演算法）

$A$ 有限維，$K=\{a\mid \exists N,\ f^Na=0\}$ 是 $m_f$ 的穩定核
（核鏈長度穩定即空間穩定）。**定理** $A_f\cong A/K$：
$K$ 是 $A\to A_f$ 的核；而 $\bar f$ 在 $A/K$ 中的乘法映射單射
（$\bar f\bar a=0\Rightarrow f a\in K\Rightarrow f^{N+1}a=0\Rightarrow a\in K$），
有限維單射自同態必滿射，故 $\bar f$ 已是可逆元，$A/K$ 滿足同一普遍性質。
演算法：矩陣冪的核迭代 + §5.3 的商。
測試核 $=$ 支集在 $Z(f)$ 的函數、$\bar f$ 取到逆元、維數 $=|D(f)|$，
以及普遍性質實例（限制映射經 $A_f$ 分解，矩陣等式）。

### 9.5 局部化的普遍性質是 iff

`extend_over_principal_localization`：給多項式映射 $k[x]\to B$（變量像），
能擴張過 $k[x]_g$ ⟺ $g$ 的像在 $B$ 是可逆元（精確單位判定）。
正例給出值、負例（像 $0$ 或零因子 $(2,0)\in k^2$）返回 `None`——
不存在的擴張不以任何「近似映射」頂替。

---

## 10. 定理 → 衍生演算法總表（連帶結果）

| 定理 | 由此得到的決策/構造程序 |
|---|---|
| Fermat 小定理 | $\mathbb F_7$ 逆元；指示多項式 $\delta_a$ |
| Buchberger 準則 + Dickson 引理 | 理想成員、理想相等判定 |
| 既約基唯一性 | 正規式陪集代表；商環良定運算 |
| 標籤變量消元 | 理想交、消失理想、簇的並 |
| Rabinowitsch 技巧 | 飽和、根成員、$D(f)$ 的閉圖、局部化同構 |
| 有限域 Nullstellensatz | 「$f$ 在 $V_{\mathbb F_7}(I)$ 消沒」的純代數判定 |
| Macaulay 階梯基 | $\dim_k R/I$、商的有限模型、結構常數化 |
| Gröbner 退化保 Krull 維數 | 維數由單項式支集組合計算 |
| CRT + $\delta_a$ 插值 | 坐標環 $=$ 函數表；$k[X]\cong\prod k$；指定值合成 |
| 乘積/餘積普遍性質 | 環配對/餘配對矩陣、簇映射配對、類型 `pairing/sum_elim` |
| $k[X\times Y]\cong k[X]\otimes k[Y]$、$k[X\sqcup Y]\cong k[X]\times k[Y]$ | 張量/直積的幾何分工，反變交換積與餘積 |
| 有限環中單射 $m_f\Rightarrow$ 滿射 | 有限代數局部化 $A_f=A/K$；$D(f)$ 維數 |
| 直積域同態由指標函數決定 | 由同態回復點映射（Spec 方向） |
| 局部化普遍性質 | 擴張存在性 ⟺ 像為可逆元（可判定） |

---

## 11. 誠實邊界（不聲稱的東西）

1. **編譯期計算**：MoonBit（v0.10.15）不是 Zig 式 comptime 語言，
   本庫不聲稱 Gröbner 在編譯期執行。真正放在編譯期的是：
   `PRIME` 常量摺疊；`Poly/Coset/LocElem/FinElem/Prod/Sum` 的類型區分；
   運算符 trait 的靜態解析與具體單態類型（算術路徑無 trait object、
   無閉包分派）；模式匹配窮盡性（餘積消去子的完備性）；
   `Option` 強制處理分母條件。
   「零成本抽象」在此的精確意思：抽象層不引入額外數學數據與動態分派——
   `Fp` 只有一個 `Int`，陪集即其正規式（另有一枚 `Int` 運行時環標籤，
   因為理想是運行時數據，這一點開銷被明寫而不隱藏）；剩下的成本全是本論運算。
2. **依賴類型不存在**：商環型別不能以理想為索引；跨商混算由標籤運行時中止，
   不由編譯器拒絕。理想在使用者執行時才給定，其他主流 CAS 亦同。
3. **點層只說 $\mathbb F_7$-點**：經典簇在代數閉包上的無窮幾何
   （如曲線的一般點）不在點列舉範圍；方程層（維數、商、冪零）才是
   通往閉包那一側的正確接口，本庫以 Krull 維數等方程量銜接。
4. **複雜度如實**：點列舉 $\Theta(7^n)$、Gröbner 基在病態例子上
   可以是雙指數、維數子集法 $\Theta(2^n)$、張量常數 $\Theta((d_Ad_B)^3)$。
   本庫定位為小變量精確計算；步數上限觸發時中止並說明，絕不回傳猜測值。
5. **局部化涵蓋**：$S=\{f^k\}$ 的一般商（飽和等式）、一點補集、
   有限代數三種已實作。任意乘法集、素理想補集的一般素譜局部化、
   分式域的一般構造（需要整環檢驗/素性判定，本庫未實作素理想判定）
   不在範圍內——需要時會返回型別不存在，而不是偷偷以叉乘冒充。
6. **未實作**：Hilbert 多項式、主分解、投射幾何、概形層語義。
   飽和測試中出現的 $(x)\cap(x,y)^2$ 式分解只是解釋那個例子的評論，
   不是分解演算法。

---

## 12. 參考

- Cox, Little, O'Shea《Ideals, Varieties, and Algorithms》：
  除法、Buchberger、消元、有限維階梯。
- Atiyah–Macdonald《Introduction to Commutative Algebra》第 2、3 章：
  張量積、局部化普遍性質。
- Eisenbud《Commutative Algebra》第 15 章：Gröbner 退化與維數。
- MoonBit 語言（安裝後本機版本 moon 0.1.20261012、moonc v0.10.15）：
  官方下載頁的 Unix 安裝腳本、方法與 trait 文件
  （含 v0.10 系列 `impl ... with fn`、`extend`、`moon.pkg` DSL 等現行語法；
  本庫語法以本機最新工具鏈的 `moon check`/`moon fmt` 為準）。
