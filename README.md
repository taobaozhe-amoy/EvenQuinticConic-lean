# EvenQuinticConic

**部分形式化项目；尚未证明原几何问题的存在性或不存在性。**

本项目尝试核查如下问题的一份候选“不存在性”论证：是否存在光滑射影、几何标准的实圆锥曲线丛
`X → ℙ²_ℝ`，其判别曲线为光滑五次曲线，判别双覆盖对应偶 theta characteristic，且实点集有两个连通分支？

当前代码已把五次式次数排除、GCD 因子分解、二次式的次数约束及齐次性连接成一个完整的多项式定理，并验证若干双覆盖、线性代数和拓扑步骤。代码还没有定义完整的几何目标，也没有从“偶 theta”推出实有理性或连通性。因此，**编译成功不表示上述问题已解决，也不验证此前整个非形式化证明**。项目不以新增公理或把目标结论作为假设的方式填补这些缺口。

## 已形式化的内容

| 模块 | 实际数学内容 | 仍未覆盖的应用步骤 |
| --- | --- | --- |
| `PolynomialDegree` | 非零五次多项式整除次数至多四的 `A*D-B²` 时，该式为零；也给出主理想版本 | 从曲线上的截面关系得到主理想成员关系；theta 的分类 |
| `RankOneFactorization` | 在 GCD 幺半群中由 `AD=B²` 推出 `A=ha², B=hab, D=hb²`，包括退化情形 | 将多项式因子转成线丛信息 |
| `ConicClassification` | 不成比例的二次式迫使 `h` 是非零常数、`a,b` 的次数至多一 | 从独立截面得到所需多项式假设 |
| `HomogeneousConics` | 将齐次二次式分解为共同非零常数乘齐次一次式的平方/乘积；接上五次式主理想关系 | 除子、线丛同构及全局截面维数 |
| `IndependentSquares` | 在代数闭域上的整代数中，线性无关的两个元素的平方仍线性无关 | 为实际线丛截面构造兼容乘法的整代数模型与限制映射 |
| `RestrictionModel` | 从实际代数同态、核等于五次式主理想及独立元素的平方/乘积像，推导完整齐次因子分解 | 为几何线丛截面构造满足这些条件的模型 |
| `CofactorCover` | 带显式 twist 参数的余子式根属于矩阵核；特征不为二时，含非零根的根集合恰有两点；在显式小行列式关系下构造根 | 判别式符号的几何识别；从余秩推出小行列式关系；覆盖的下降、étale 性与 theta 对应 |
| `IsotropicDimension` | 维数和超过环境维数的子空间有非零交；显式分裂二次型的五维子空间限制各向同性 | 从 Clifford 指数和序得到 Pfister 邻形式并证明分裂 |
| `Incidence` | 非零 `2×2` 小行列式条件下，两条齐次线性方程有唯一规范化解，并给出集合等价 | 非空稠密开集、正则映射、概形同构及实双有理性 |
| `ConnectedComponents` | 实际拓扑连通分支商 `ConnectedComponents X` 在 `ConnectedSpace X` 假设下基数为一 | 为所研究的实代数簇证明该连通性假设 |

特别地，`ConnectedComponents` 中的连通性是**显式假设**；这个模块没有从圆锥曲线丛的几何条件推出连通性。

## 本轮接通的证明链

`nonproportional_homogeneous_conics_from_quintic_ideal` 的精确内容是：在任意域上的真正多元多项式环中，若 `deg F=5`，`A,B,D` 是齐次二次式，`A,D` 非零且不成标量比例，并且 `AD-B² ∈ (F)`，则存在 `c≠0` 和齐次一次式 `a,b`，使

$$
A=c a^2,\qquad B=c ab,\qquad D=c b^2.
$$

这里理想成员关系与不成比例条件都是明确假设。定理没有把“在曲线上恒等”未经证明地替换为“属于定义理想”。

更进一步，`homogeneous_conic_lifts_factor_of_principal_quintic_kernel` 使用真实的代数同态 `φ : K[σ] →ₐ[K] R`，假设其核为 `(F)`，且 `φ(A)=s², φ(B)=st, φ(D)=t²`、`s,t` 线性无关。它在代数闭基域与整代数假设下，内部推导上述理想关系、非零性和非比例性，再得到同一个齐次分解。实际几何截面的这种兼容模型仍待构造。

余子式方程现在写作 `vᵢvⱼ=twist*adj(M)ᵢⱼ`。正、负两种选择都被支持；代码没有把三阶矩阵的负号约定自动移用于目标五阶矩阵。

## 构建与审计

环境固定为 Lean `v4.24.0` 和 mathlib 提交
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。提交的 `lake-manifest.json` 固定传递依赖。

安装 [elan](https://github.com/leanprover/elan) 后，在项目根目录运行：

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

`Audit.lean` 枚举 `EvenQuinticConic` 命名空间内的声明，递归收集其公理依赖；除 Lean/mathlib 常用的 `propext`、`Classical.choice`、`Quot.sound` 外，出现任何公理均使审计失败。这会拒绝 `sorryAx` 及项目自定义公理。审计通过仅保证代码中精确命题的依赖，不能保证它们与非形式化几何论证相同。

GitHub Actions 配置见 `.github/workflows/lean.yml`。其运行相同构建和审计命令。实际本地验证记录见 `verification/`；未在 GitHub 上运行前，不声称远程 CI 已通过。

## 后续证明任务

完整论证的缺口列于 [docs/PROOF_GAPS.md](docs/PROOF_GAPS.md)，固定版本 mathlib 的能力检查见 [docs/MATHLIB_STATUS.md](docs/MATHLIB_STATUS.md)。这些文档中的数学叙述均不是 Lean 已验证的定理。

用户提供的参考项目是 [RealConicBundles-Problem3-lean](https://github.com/fanyh27/RealConicBundles-Problem3-lean)。本次对比使用提交 `8b2e7df967727bf82d1c3430128b928e338c31b9`：其 README 明确不附加偶 theta、几何有理性或相对 Picard 秩的要求。本项目不据此否定那个项目实际陈述的结论；比较两个项目时必须先对齐定理假设。

## English scope note

This repository contains independently checkable lemmas from an attempted obstruction argument for real conic bundles with smooth quintic discriminant and even theta characteristic. It is **not** a formal proof of the geometric obstruction, nor a construction of an example. All geometric bridges listed in `docs/PROOF_GAPS.md` remain unformalized. In particular, the final connectedness assumption has not been deduced from the original hypotheses.
