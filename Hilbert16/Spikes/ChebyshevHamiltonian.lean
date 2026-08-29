import Hilbert16.Spikes.ChebyshevDensity

set_option autoImplicit false

namespace Hilbert16.Spikes

/-- Paper Eq. (3.1): the anisotropic Chebyshev Hamiltonian. -/
noncomputable def chebyshevHamiltonian (n : ℕ) (lambda : ℝ) (z : ℝ × ℝ) : ℝ :=
  ((Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.1 ^ 2 +
    lambda * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.2 ^ 2) / 2

/-- The center indexed by the pair of Chebyshev roots `(i,j)`. -/
noncomputable def chebyshevCenterPoint (n i j : ℕ) : ℝ × ℝ :=
  (Real.cos (chebyshevRootPhase n i), Real.cos (chebyshevRootPhase n j))

theorem chebyshevRootPhase_mem_Ioo
    {n i : ℕ} (hn : n ≠ 0) (hi : i < n) :
    chebyshevRootPhase n i ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have h := chebyshevInverseBranch_angle_mem_Ioo hn hi
    (u := (0 : ℝ)) (by norm_num)
  simpa using h

theorem chebyshevRootPhase_lt
    {n i j : ℕ} (hn : n ≠ 0) (hij : i < j) :
    chebyshevRootPhase n i < chebyshevRootPhase n j := by
  have hnPos : 0 < (2 : ℝ) * (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    positivity
  unfold chebyshevRootPhase
  apply (div_lt_div_iff_of_pos_right hnPos).2
  have hijReal : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  push_cast
  nlinarith [Real.pi_pos]

theorem chebyshevRootCoordinate_injective
    {n : ℕ} (hn : n ≠ 0) :
    Function.Injective
      (fun i : Fin n => Real.cos (chebyshevRootPhase n i)) := by
  intro i j heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hphase := chebyshevRootPhase_lt hn hij
    have hiPhase := chebyshevRootPhase_mem_Ioo hn i.isLt
    have hjPhase := chebyshevRootPhase_mem_Ioo hn j.isLt
    have hcos := Real.strictAntiOn_cos
      ⟨hiPhase.1.le, hiPhase.2.le⟩ ⟨hjPhase.1.le, hjPhase.2.le⟩ hphase
    exact (ne_of_gt hcos) heq
  · have hphase := chebyshevRootPhase_lt hn hji
    have hiPhase := chebyshevRootPhase_mem_Ioo hn i.isLt
    have hjPhase := chebyshevRootPhase_mem_Ioo hn j.isLt
    have hcos := Real.strictAntiOn_cos
      ⟨hjPhase.1.le, hjPhase.2.le⟩ ⟨hiPhase.1.le, hiPhase.2.le⟩ hphase
    exact (ne_of_lt hcos) heq

/-- The `n` indexed simple roots, packaged as an embedding. -/
noncomputable def chebyshevRootEmbedding (n : ℕ) (hn : n ≠ 0) : Fin n ↪ ℝ :=
  ⟨fun i => Real.cos (chebyshevRootPhase n i), chebyshevRootCoordinate_injective hn⟩

/-- The product embedding of the `n²` indexed centers. -/
noncomputable def chebyshevCenterEmbedding
    (n : ℕ) (hn : n ≠ 0) : Fin n × Fin n ↪ ℝ × ℝ :=
  Function.Embedding.prodMap (chebyshevRootEmbedding n hn) (chebyshevRootEmbedding n hn)

/-- The actual finite set of all indexed Chebyshev centers. -/
noncomputable def chebyshevCenterGrid (n : ℕ) (hn : n ≠ 0) : Finset (ℝ × ℝ) :=
  (Finset.univ.product Finset.univ).map (chebyshevCenterEmbedding n hn)

theorem chebyshevCenterGrid_card (n : ℕ) (hn : n ≠ 0) :
    (chebyshevCenterGrid n hn).card = n ^ 2 := by
  simp [chebyshevCenterGrid, pow_two]

theorem chebyshevRoot_isRoot
    {n i : ℕ} (hi : i < n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).IsRoot
      (Real.cos (chebyshevRootPhase n i)) := by
  have hmult := Polynomial.Chebyshev.rootMultiplicity_T_real hi
  have hroot : (Polynomial.Chebyshev.T ℝ (n : ℤ)).IsRoot
      (Real.cos (((2 * (i : ℝ) + 1) * Real.pi) / (2 * (n : ℝ)))) :=
    (Polynomial.rootMultiplicity_pos
      (Polynomial.Chebyshev.T_ne_zero ℝ (n : ℤ))).mp (by
        rw [hmult]
        norm_num)
  convert hroot using 1
  simp [chebyshevRootPhase]

theorem eval_chebyshev_at_root
    {n i : ℕ} (hi : i < n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
      (Real.cos (chebyshevRootPhase n i)) = 0 :=
  (chebyshevRoot_isRoot hi).eq_zero

theorem eval_derivative_chebyshev_at_root_ne_zero
    {n i : ℕ} (hn : n ≠ 0) (hi : i < n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
      (Real.cos (chebyshevRootPhase n i)) ≠ 0 := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  let x := Real.cos (chebyshevRootPhase n i)
  have hroot : p.IsRoot x := chebyshevRoot_isRoot hi
  have hmult : p.rootMultiplicity x = 1 := by
    convert Polynomial.Chebyshev.rootMultiplicity_T_real hi using 1
    simp [p, x, chebyshevRootPhase]
  have hderivMult : p.derivative.rootMultiplicity x = 0 := by
    rw [Polynomial.derivative_rootMultiplicity_of_root hroot, hmult]
  have hdegree : p.natDegree = n := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    simpa only [p, Int.natAbs_natCast] using
      (Polynomial.Chebyshev.degree_T ℝ (n : ℤ))
  have hderivPoly : p.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero, hdegree]
    exact hn
  intro heval
  have hderivRoot : p.derivative.IsRoot x := heval
  have hpos := (Polynomial.rootMultiplicity_pos hderivPoly).mpr hderivRoot
  rw [hderivMult] at hpos
  exact (Nat.lt_irrefl 0) hpos

/-- The Hamiltonian vanishes at every indexed center. -/
theorem chebyshevHamiltonian_center_eq_zero
    {n i j : ℕ} (hi : i < n) (hj : j < n) (lambda : ℝ) :
    chebyshevHamiltonian n lambda (chebyshevCenterPoint n i j) = 0 := by
  simp [chebyshevHamiltonian, chebyshevCenterPoint,
    eval_chebyshev_at_root hi, eval_chebyshev_at_root hj]

/-- First coordinate of the Hamiltonian gradient. -/
noncomputable def chebyshevHamiltonianDx (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.1 *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval z.1

/-- Second coordinate of the Hamiltonian gradient. -/
noncomputable def chebyshevHamiltonianDy (n : ℕ) (lambda : ℝ) (z : ℝ × ℝ) : ℝ :=
  lambda * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.2 *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval z.2

theorem chebyshevHamiltonianDx_center_eq_zero
    {n i j : ℕ} (hi : i < n) :
    chebyshevHamiltonianDx n (chebyshevCenterPoint n i j) = 0 := by
  simp [chebyshevHamiltonianDx, chebyshevCenterPoint, eval_chebyshev_at_root hi]

theorem chebyshevHamiltonianDy_center_eq_zero
    {n i j : ℕ} (hj : j < n) (lambda : ℝ) :
    chebyshevHamiltonianDy n lambda (chebyshevCenterPoint n i j) = 0 := by
  simp [chebyshevHamiltonianDy, chebyshevCenterPoint, eval_chebyshev_at_root hj]

/-- The diagonal Hessian quadratic form at a Chebyshev center. -/
noncomputable def chebyshevCenterHessianQuadratic
    (n i j : ℕ) (lambda : ℝ) (xi : ℝ × ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
      (Real.cos (chebyshevRootPhase n i)) ^ 2 * xi.1 ^ 2 +
    lambda * (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
      (Real.cos (chebyshevRootPhase n j)) ^ 2 * xi.2 ^ 2

/-- Paper Eq. (3.2): the Hessian at every indexed center is positive definite when `lambda>0`. -/
theorem chebyshevCenterHessianQuadratic_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda : ℝ} (hlambda : 0 < lambda) {xi : ℝ × ℝ} (hxi : xi ≠ 0) :
    0 < chebyshevCenterHessianQuadratic n i j lambda xi := by
  have hdi := eval_derivative_chebyshev_at_root_ne_zero hn hi
  have hdj := eval_derivative_chebyshev_at_root_ne_zero hn hj
  by_cases hxi1 : xi.1 = 0
  · have hxi2 : xi.2 ≠ 0 := by
      intro hzero
      apply hxi
      apply Prod.ext <;> simp [hxi1, hzero]
    have hsecond : 0 < lambda *
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
          (Real.cos (chebyshevRootPhase n j)) ^ 2 * xi.2 ^ 2 := by
      positivity
    unfold chebyshevCenterHessianQuadratic
    rw [hxi1]
    norm_num
    exact hsecond
  · have hfirst : 0 <
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
          (Real.cos (chebyshevRootPhase n i)) ^ 2 * xi.1 ^ 2 := by
      positivity
    have hsecond : 0 ≤ lambda *
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
          (Real.cos (chebyshevRootPhase n j)) ^ 2 * xi.2 ^ 2 := by
      positivity
    unfold chebyshevCenterHessianQuadratic
    linarith

/-- In the product inverse-branch coordinates the Hamiltonian is exactly the elliptic quadratic
energy. -/
theorem chebyshevHamiltonian_inverseMap_eq
    {n i j : ℕ} (hn : n ≠ 0) {lambda : ℝ} {z : ℝ × ℝ}
    (hu : |z.1| ≤ 1) (hv : |z.2| ≤ 1) :
    chebyshevHamiltonian n lambda (chebyshevCellInverseMap n i j z) =
      (z.1 ^ 2 + lambda * z.2 ^ 2) / 2 := by
  change ((Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (chebyshevInverseBranch n i z.1) ^ 2 +
      lambda * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (chebyshevInverseBranch n j z.2) ^ 2) / 2 = _
  rw [eval_chebyshevInverseBranch hn hu, eval_chebyshevInverseBranch hn hv]

theorem chebyshevHamiltonian_inverseMap_lt_iff
    {n i j : ℕ} (hn : n ≠ 0) {lambda h : ℝ} {z : ℝ × ℝ}
    (hu : |z.1| ≤ 1) (hv : |z.2| ≤ 1) :
    chebyshevHamiltonian n lambda (chebyshevCellInverseMap n i j z) < h ↔
      z ∈ ellipticEnergyDisk lambda h := by
  rw [chebyshevHamiltonian_inverseMap_eq hn hu hv]
  unfold ellipticEnergyDisk
  change (z.1 ^ 2 + lambda * z.2 ^ 2) / 2 < h ↔
    z.1 ^ 2 + lambda * z.2 ^ 2 < 2 * h
  constructor <;> intro H <;> nlinarith

end Hilbert16.Spikes
