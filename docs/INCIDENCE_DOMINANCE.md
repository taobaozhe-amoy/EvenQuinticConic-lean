# 实际关联开集对参数平面的支配性

本阶段证明矩阵网构造中的实际有理开集支配参数平面。它补上此前明确保留的支配性缺口；仍未从原题的 even theta 假设构造矩阵网和公共实点，也没有完成原圆锥丛的比较及实连通性。

## 精确端点

`exists_dominant_rational_globalIncidenceOpen_of_common_point` 接收：

- 无限域 `K`，且 `2 ≠ 0`；
- 三个实际对称 `5 × 5` 矩阵 `Mᵢ`；
- 非零公共各向同性向量 `P`，即 `PᵀMᵢP=0`；
- 实际行列式 `D(T)=det(Σ TᵢMᵢ)` 的几何 Jacobian 条件，以 `ProjectiveJacobianCertificate D` 表达。

它构造可逆矩阵 `B`，首列为 `P`，以及变换后实际全局关联概形 `Z` 的非空整开集 `U`，并证明：

1. `U` 的实际参数投影 `globalIncidenceMinorParameterProjection` 到 `Proj K[T₀,T₁,T₂]` 是 `IsDominant`，即像稠密；
2. `U` 的实际仿射坐标代数 `S` 是整环，且 `FractionRing S ≃ₐ[K] K(u,v,w)`。

实际开图同构、基域结构相容性沿用已经编译的全局开图构造。非零子式、可逆坐标变换、剩余二次多项式的非零性、参数拉回单射及支配性均在端点内部推出。

## 核查中发现并修正的假设差别

此前非空有理开集端点只检查 `K` 值向量上的 Jacobian 条件。支配性证明需要在参数生成的扩域上应用它，不能把基域点条件直接升级为几何条件。

本阶段定义实际 Jacobian 理想

\[
J(D)=(D,\partial_0D,\partial_1D,\partial_2D),
\]

并令 certificate 为每个 `Tᵢ ∈ √J(D)`。代码通过 Nullstellensatz 证明，这与下面的几何点条件等价：

\[
\forall t\in\overline K^3\setminus\{0\},\quad
D(t)=0\Longrightarrow\exists i\;\partial_iD(t)\ne0.
\]

证书向任意扩域传递，并在可逆矩阵合同变换下保持。这里检查的是实际行列式方程，不能用其约化零集光滑替代。原题的几何光滑性到这个具体行列式方程的桥梁仍属于原对象实例化工作，未在本阶段假装完成。

## 支配性如何证明

令 `L=K(x₀,x₁,x₂)` 是已构造开集的有理函数域。实际参数投影给出两个有理函数 `s₀,s₁∈L`，令 `F=K(s₀,s₁)`。这些函数直接来自 Segre 列坐标的拉回和已证 Cramer 消元同构，没有另选任意参数函数。

1. 归一化后的参数向量 `t∈F³` 有一个坐标为 `1`。实际泛空间坐标 `y` 满足极线方程和尾部二次方程。
2. 几何 Jacobian 条件在 `F` 上保证实际矩阵 `A(t)` 的伴随矩阵非零。公共点处极化行的线性无关性，加上实际极线关系，保证所选仿射图中至少一个线性系数非零。
3. 消去这个仿射变量，得到具体的 `G∈F[u,v]`。代码证明 `G≠0`：如果极超平面上的二次限制为零，原矩阵将通过二维空间分解，迫使全部四阶余子式为零，与伴随矩阵非零矛盾。坐标置换、去齐次化及消元代入都在实际多项式上完成。
4. 两个剩余空间坐标满足 `G=0`，且生成 `L/F`，所以 `trdeg_F L≤1`。结合 `trdeg_K L=3` 和超越次数塔公式，推出 `s₀,s₁` 在 `K` 上代数独立。
5. 因而实际参数坐标环拉回单射。素谱的稠密像判据及射影标准图的稠密性，给出实际概形态射 `U→ℙ²_K` 的支配性。

注意，仅有 `adj(A)≠0` 不足以保证极线系数非零，例如 `diag(0,1,1,1,1)`。代码分别证明了第 2 步需要的极化独立性，没有使用这个错误推断。

## 代码对应

| 文件 | 已证明的作用 |
| --- | --- |
| `GeometricJacobianTransfer` / `IncidenceJacobianCongruence` | 几何点条件与根理想证书等价，扩域传递及合同变换保持 |
| `IncidenceFiberNondegeneracy` / `IncidenceGeometricFibers` | 二维因子分解迫使伴随矩阵为零；实际几何 Jacobian 保证非零伴随矩阵 |
| `IncidenceGenericFiber` / `IncidenceLinearElimination` | 实际极超平面限制、任意坐标图消元及剩余二次多项式非零 |
| `IncidenceTranscendence` | 从线性消元及非零剩余多项式关系推导参数代数独立 |
| `IncidenceParameterProjection` / `IncidenceParameterFunctionField` | 实际参数概形态射、其拉回及实际生成子域，原关联方程的泛点关系 |
| `IncidenceDominance` | 从矩阵网和几何 Jacobian 输入直接推出实际投影支配 |
| `GlobalDominantIncidenceChart` | 从任意公共点组装非空整、有理且支配参数平面的全局开集 |

## 尚未证明

仍未证明整个 `Z` 不可约，或 `U` 在整个 `Z` 中稠密；本结果只对已构造的具体开集给出支配态射。尚未构造全 `Z` 上的参数投影并完成泛纤维与原圆锥丛的比较。Brauer 类识别、原判别双覆盖与 theta 的对应、产生所需公共实点的二次型论证，以及最终实连通性也仍未全部形式化。

因此，新增结论是一条有完整 Lean 证明的几何中间定理，不是原题已解决的声明。


## 2026-10-17：后续理论路线简化

[本轮理论证明](THEORETICAL_PROOF_REVIEW_2026_10_17.md) 已给出条件性的后半段推导：
从这里的实际支配开集直接取泛纤维，得到非空开浸入 \(U_\eta\subset C_r\)；
局部化恒等式 \(\operatorname{Frac}(T^{-1}B)=\operatorname{Frac}B\) 保持参数域，
从而 \(\mathbb R(U)=F(C_r)\)。结合实际 Clifford/Brauer 比较，识别原圆锥丛的函数域。

因此，上节列出的整个 \(Z\) 不可约、\(U\) 在其中稠密，以及在全 \(Z\) 上构造参数投影，
不再是这条后续路线必须完成的形式化目标。泛纤维与函数域的实际识别及原几何输入仍待
Lean 证明；上述纸面推导没有改变本文件端点的输入或扩大其内核已验证结论。

## 后续形式化：实际泛参数基变换

[实际泛纤维模块](INCIDENCE_GENERIC_FIBER.md) 现在已经构造上述原参数投影的
泛参数 pullback，并将它与参数局部化的谱同构，两条投影均相容。
`exists_integral_genericFiber_of_common_point` 从本文件相同的矩阵网、公共点及
几何 Jacobian 输入，直接推出实际泛基变换的非空和整性。函数域局部化同构
保持整个参数分式域的作用；实际参数域识别、泛矩阵行列式非零及基变换后的
实际线性、二次方程和子式也已处理。与射影圆锥曲线开集的组装比较及原圆锥丛
比较仍未完成，原问题的完整形式化状态未因此改变。
