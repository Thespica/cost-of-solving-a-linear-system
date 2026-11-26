# 一个线性方程组解坐标的算术复杂度

给定可逆的 $d\times d$ 矩阵 $A$，只要求返回 $Ax=e_1$ 的第一个坐标。这个仓库用 Lean 4 验证一个条件下界。把下面两条文献定理作为参数，对于每个 $d\ge 8$，任何在所有可逆输入上精确答对的固定四则运算程序，其门数 $s$ 满足

$$
\lfloor d/4\rfloor^9\le (18s)^4,
\qquad
s\ge \frac{d^{9/4}}{2304}.
$$

门数包括加、减、乘、除。程序可以使用底域中的任意常数，可以多次读取同一寄存器。每次除法都要求除数非零。程序是固定的直线程序，每个门的运算和两个操作数在读入矩阵前就已确定。具体输入版本覆盖无限域，包括有理数域。Lean 用 `n+1` 表示维数，使第一个坐标始终有定义。

[英文短文（PDF）](output/pdf/single-coordinate.pdf) · [LaTeX 源码](paper/single-coordinate.tex)

## 两条外部定理

两条前提共享函数 `rank : ℕ → ℕ`。代入文献时，`rank k` 表示边长 $k$ 的方阵乘法张量在复数上的边界秩。Lean 的归约对任何满足这两条前提的函数都成立。

- **AndrewsBound** 是 Andrews 定理 3.4 在方阵行列式理想上的特例。每个输出非零行列式倍数的无除法多项式程序，若用了 $m$ 个乘法门，则 $\mathrm{rank}(\lfloor d/4\rfloor)\le 6m$。这里计全部乘法，程序的精确成本给原定理中的边界乘法复杂度提供上界。有理系数电路也可视为复系数电路。[Andrews 原文，第 14 页](https://arxiv.org/pdf/2208.01078#page=14)
- **MatrixRankBound** 把矩阵乘法预印本逐尺寸的边界秩下界写成整数不等式 $k^9\le \mathrm{rank}(k)^4$，适用于 $k\ge 2$。仓库将这条结论作为显式前提。OpenAI 公布的 Lean 主接口陈述的是无除法程序的渐近指数，本项目直接使用论文所需的边界秩表述。[预印本及 Lean 范围](https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/README.md)

## Lean 验证了哪些步骤

1. 程序可以用带界下标读取先前寄存器。逐门记录分子、分母，将每个源门转换为至多三个乘法门。转换保留共享，末尾可以证明存在一个具备该乘法门数界的无除法程序。[程序](SingleCoordinate/Programs.lean) · [清分母](SingleCoordinate/Circuits.lean)
2. 第一个解坐标等于左上角元素的余子式除以行列式。Lean 证明二者的公因子都是单位。设公因子为 $p$。第一个余子式与第一行无关，因此改变第一行也保持 $p$ 不变。依次用每个单位行替换第一行，得到 $p$ 整除该行的所有余子式。对每列都有一个与该列无关的非零余子式，因此将整列置零仍保持 $p$ 不变。各列都置零后只剩常数。[替换的引理](SingleCoordinate/Specialize.lean) · [矩阵证明](SingleCoordinate/Matrix.lean)
3. 程序输出的分母非零。由交叉相乘和上述互素性，行列式整除分母。将两条外部前提代入即可得到逐维数的整数界。[归约](SingleCoordinate/LowerBound.lean)
4. 对具体矩阵也验证了这一步。单位阵上的合法求值足以排除符号程序中恒为零的除数。在所有可逆矩阵上答对，意味着清分母后的等式在这些矩阵上成立。将两边之差再乘行列式，就得到在奇异矩阵上也成立的等式。无限域上的多项式恒等原理给出形式证明。[具体输入](SingleCoordinate/Numerical.lean) · [实数指数下界](SingleCoordinate/Exponent.lean)

## 复现

项目固定 Lean 4.19.0 和 Mathlib 提交 `c44e0c8ee63ca166450922a373c7409c5d26b00b`。在仓库根目录运行

```sh
./scripts/verify
```

脚本构建整个库，使用二阶矩阵检查寄存器重用和除零条件，并审计最终定理的公理依赖。当前本地工作副本配有忽略跟踪的工具链和依赖缓存。新克隆可以使用 elan 提供的 `lake`。实数指数下界与更精细的整数界都可以独立检查。[实数下界](SingleCoordinate/Exponent.lean) · [整数下界](SingleCoordinate/Numerical.lean)
