import Mathlib

open Set Topology MeasureTheory

noncomputable section HybridDiscretizationVerification

section HybridSpaceTheory

/-- Гибридная норма (формула 1) на прямой сумме X = L₁(Ω, Σ, μ) × ℓ₁(ℕ):
    ‖(x_c, x_d)‖_X = ‖x_c‖_{L₁} + ‖x_d‖_{ℓ₁} -/
def HybridNorm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Lp ℝ 1 μ × lp (fun _ : ℕ => ℝ) 1) : ℝ :=
  ‖x.1‖ + ‖x.2‖

/-- Ортогональность по Биркгофу–Джеймсу в гибридном пространстве:
    x ⊥_B V ⇔ ∀ v ∈ V, ∀ c ∈ ℝ, ‖x‖_X ≤ ‖x + c • v‖_X -/
def HybridBirkhoffOrthogonal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Lp ℝ 1 μ × lp (fun _ : ℕ => ℝ) 1)
    (V : Submodule ℝ (Lp ℝ 1 μ × lp (fun _ : ℕ => ℝ) 1)) : Prop :=
  ∀ v ∈ V, ∀ c : ℝ, HybridNorm μ x ≤ HybridNorm μ (x + c • v)

/-- Вспомогательная лемма: t * sign(t) = |t| -/
lemma real_mul_sign_eq_abs (t : ℝ) : t * Real.sign t = |t| := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht, mul_neg_one]
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht, mul_one]

/-- ТЕОРЕМА 1 (Необходимость, неравенство 2):
    Если существует совместный аннулирующий функционал g = (g_c, g_d) ∈ ∂‖u‖_X
    с ‖g_c‖_∞ ≤ 1 и ‖g_d‖_∞ ≤ 1, совпадающий со sign(u) вне нулей u,
    то выполнено совместное знаково-взвешенное интегрально-дискретное неравенство (2). -/
theorem hybrid_necessity_joint_ineq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u v : Lp ℝ 1 μ × lp (fun _ : ℕ => ℝ) 1)
    (g_c : Ω → ℝ) (g_d : ℕ → ℝ)
    (hgc_meas : StronglyMeasurable g_c)
    (hgc_bound : ∀ᵐ t ∂μ, |g_c t| ≤ 1)
    (hgd_bound : ∀ n : ℕ, |g_d n| ≤ 1)
    (hgc_sign : ∀ᵐ t ∂μ, (u.1 : Ω → ℝ) t ≠ 0 → g_c t = Real.sign ((u.1 : Ω → ℝ) t))
    (hgd_sign : ∀ n : ℕ, u.2 n ≠ 0 → g_d n = Real.sign (u.2 n))
    (h_annihilate : (∫ t, (v.1 : Ω → ℝ) t * g_c t ∂μ) + (∑' n : ℕ, v.2 n * g_d n) = 0)
    (h_meas_supp : MeasurableSet { t : Ω | (u.1 : Ω → ℝ) t = 0 })
    (h_summ_vd : Summable (fun n : ℕ => |v.2 n|)) :

    |(∫ t in { t : Ω | (u.1 : Ω → ℝ) t = 0 }ᶜ, (v.1 : Ω → ℝ) t * Real.sign ((u.1 : Ω → ℝ) t) ∂μ) +
      (∑' n : { n : ℕ | u.2 n ≠ 0 }, v.2 n * Real.sign (u.2 n))| ≤
    (∫ t in { t : Ω | (u.1 : Ω → ℝ) t = 0 }, |(v.1 : Ω → ℝ) t| ∂μ) +
      (∑' n : { n : ℕ | u.2 n = 0 }, |v.2 n|) := by
  set Sc₀ : Set Ω := { t : Ω | (u.1 : Ω → ℝ) t = 0 }
  set Sd_supp : Set ℕ := { n : ℕ | u.2 n ≠ 0 }
  have h_compl_eq : Sd_suppᶜ = { n : ℕ | u.2 n = 0 } := by
    ext n; simp [Sd_supp]
  have h_int_vcgc : Integrable (fun t => (v.1 : Ω → ℝ) t * g_c t) μ := by
    simpa only [mul_comm] using (L1.integrable_coeFn v.1).bdd_mul hgc_meas.aestronglyMeasurable
      (hgc_bound.mono fun _ h => by rwa [Real.norm_eq_abs])
  have h_summ_vdgd : Summable (fun n : ℕ => v.2 n * g_d n) := by
    refine Summable.of_norm_bounded h_summ_vd fun n => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hgd_bound n)
  have h_int_split : (∫ t in Sc₀ᶜ, (v.1 : Ω → ℝ) t * g_c t ∂μ) +
      (∫ t in Sc₀, (v.1 : Ω → ℝ) t * g_c t ∂μ) = ∫ t, (v.1 : Ω → ℝ) t * g_c t ∂μ := by
    rw [add_comm, integral_add_compl h_meas_supp h_int_vcgc]
  have h_sum_split : (∑' n : Sd_supp, v.2 n * g_d n) +
      (∑' n : { n : ℕ | u.2 n = 0 }, v.2 n * g_d n) = ∑' n : ℕ, v.2 n * g_d n := by
    have h1 := Summable.tsum_subtype_add_tsum_subtype_compl h_summ_vdgd Sd_supp
    rwa [h_compl_eq] at h1
  have h_ic_eq : ∫ t in Sc₀ᶜ, (v.1 : Ω → ℝ) t * g_c t ∂μ =
      ∫ t in Sc₀ᶜ, (v.1 : Ω → ℝ) t * Real.sign ((u.1 : Ω → ℝ) t) ∂μ := by
    refine setIntegral_congr_ae h_meas_supp.compl ?_
    filter_upwards [hgc_sign] with t ht hut
    rw [ht hut]
  have h_sd_eq : (∑' n : Sd_supp, v.2 n * g_d n) =
      ∑' n : Sd_supp, v.2 n * Real.sign (u.2 n) := by
    congr 1; ext ⟨n, hn⟩; rw [hgd_sign n hn]
  have h_balance : ((∫ t in Sc₀ᶜ, (v.1 : Ω → ℝ) t * Real.sign ((u.1 : Ω → ℝ) t) ∂μ) +
      (∑' n : Sd_supp, v.2 n * Real.sign (u.2 n))) =
      -((∫ t in Sc₀, (v.1 : Ω → ℝ) t * g_c t ∂μ) +
        (∑' n : { n : ℕ | u.2 n = 0 }, v.2 n * g_d n)) := by
    rw [← h_ic_eq, ← h_sd_eq]
    linarith
  rw [h_balance, abs_neg]
  have h_sub_vdgd : Summable (fun n : { n : ℕ | u.2 n = 0 } => v.2 n * g_d n) :=
    h_summ_vdgd.subtype (fun n => u.2 n = 0)
  have h_sub_vd : Summable (fun n : { n : ℕ | u.2 n = 0 } => |v.2 n|) :=
    h_summ_vd.subtype (fun n => u.2 n = 0)
  calc |(∫ t in Sc₀, (v.1 : Ω → ℝ) t * g_c t ∂μ) + (∑' n : { n : ℕ | u.2 n = 0 }, v.2 n * g_d n)|
    _ ≤ |∫ t in Sc₀, (v.1 : Ω → ℝ) t * g_c t ∂μ| + |∑' n : { n : ℕ | u.2 n = 0 }, v.2 n * g_d n| :=
        abs_add_le _ _
    _ ≤ (∫ t in Sc₀, |(v.1 : Ω → ℝ) t * g_c t| ∂μ) + (∑' n : { n : ℕ | u.2 n = 0 }, |v.2 n * g_d n|) := by
        refine add_le_add abs_integral_le_integral_abs ?_
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm h_sub_vdgd.norm
    _ ≤ (∫ t in Sc₀, |(v.1 : Ω → ℝ) t| ∂μ) + (∑' n : { n : ℕ | u.2 n = 0 }, |v.2 n|) := by
        refine add_le_add ?_ ?_
        · refine setIntegral_mono_ae_restrict h_int_vcgc.integrableOn.abs
            (L1.integrable_coeFn v.1).integrableOn.abs ?_
          filter_upwards [ae_restrict_of_ae hgc_bound] with t ht
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) ht
        · refine Summable.tsum_le_tsum (fun ⟨n, _⟩ => ?_) h_sub_vdgd.abs h_sub_vd
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hgd_bound n)
/-- Вспомогательная лемма: норма в пространстве ℓ₁(ℕ) равна ряду модулей ∑' n, |x(n)| -/
lemma lp1_norm_eq_tsum_abs (x : lp (fun _ : ℕ => ℝ) 1) :
    ‖x‖ = ∑' n : ℕ, |x n| := by
  have h1 := lp.norm_rpow_eq_tsum (by simp : 0 < (1 : ENNReal).toReal) x
  simpa [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using h1

/-- Вспомогательная лемма: ряд модулей координат элемента ℓ₁(ℕ) сходится -/
lemma lp1_summable_abs (x : lp (fun _ : ℕ => ℝ) 1) :
    Summable (fun n : ℕ => |x n|) := by
  have h_summ := lp.memℓp x
  rw [memℓp_gen_iff (by simp : 0 < (1 : ENNReal).toReal)] at h_summ
  simpa [Real.norm_eq_abs] using h_summ

/-- ТЕОРЕМА 1 (Достаточность, двойственный этап):
    Если для элемента u = (u_c, u_d) ∈ U существует совместный функционал g = (g_c, g_d)
    с ‖g_c‖_∞ ≤ 1, ‖g_d‖_∞ ≤ 1, совпадающий со sign(u) на носителях и аннулирующий V,
    то u ⊥_B V в гибридной норме ‖·‖_X. -/
theorem hybrid_sufficiency_birkhoff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Submodule ℝ (Lp ℝ 1 μ × lp (fun _ : ℕ => ℝ) 1))
    (u : Lp ℝ 1 μ × lp (fun _ : ℕ => ℝ) 1)
    (g_c : Ω → ℝ) (g_d : ℕ → ℝ)
    (hgc_meas : StronglyMeasurable g_c)
    (hgc_bound : ∀ᵐ t ∂μ, |g_c t| ≤ 1)
    (hgd_bound : ∀ n : ℕ, |g_d n| ≤ 1)
    (hgc_sign : ∀ᵐ t ∂μ, (u.1 : Ω → ℝ) t ≠ 0 → g_c t = Real.sign ((u.1 : Ω → ℝ) t))
    (hgd_sign : ∀ n : ℕ, u.2 n ≠ 0 → g_d n = Real.sign (u.2 n))
    (h_annihilate : ∀ v ∈ V, (∫ t, (v.1 : Ω → ℝ) t * g_c t ∂μ) + (∑' n : ℕ, v.2 n * g_d n) = 0) :
    HybridBirkhoffOrthogonal μ u V := by
  intro v hv c
  unfold HybridNorm
  have h_norm_uc : ‖u.1‖ = ∫ t, (u.1 : Ω → ℝ) t * g_c t ∂μ := by
    have h1 : ‖u.1‖ = ∫ t, |(u.1 : Ω → ℝ) t| ∂μ := by
      simpa [Real.norm_eq_abs] using L1.norm_eq_integral_norm u.1
    rw [h1]
    apply integral_congr_ae
    filter_upwards [hgc_sign] with t ht
    by_cases hut : (u.1 : Ω → ℝ) t = 0
    · simp [hut]
    · rw [ht hut, real_mul_sign_eq_abs]
  have h_norm_ud : ‖u.2‖ = ∑' n : ℕ, u.2 n * g_d n := by
    rw [lp1_norm_eq_tsum_abs u.2]
    congr 1; ext n
    by_cases hun : u.2 n = 0
    · simp [hun]
    · rw [hgd_sign n hun, real_mul_sign_eq_abs]
  have h_int_prod : ∀ w : Lp ℝ 1 μ, Integrable (fun t => (w : Ω → ℝ) t * g_c t) μ := by
    intro w
    simpa only [mul_comm] using (L1.integrable_coeFn w).bdd_mul hgc_meas.aestronglyMeasurable
      (hgc_bound.mono fun _ h => by rwa [Real.norm_eq_abs])
  have h_summ_prod : ∀ w : lp (fun _ : ℕ => ℝ) 1, Summable (fun n => w n * g_d n) := by
    intro w
    refine Summable.of_norm_bounded (lp1_summable_abs w) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hgd_bound n)
  have h_cont_est : ∫ t, (u.1 : Ω → ℝ) t * g_c t ∂μ + c * ∫ t, (v.1 : Ω → ℝ) t * g_c t ∂μ ≤ ‖u.1 + c • v.1‖ := by
    have h_ae : ∀ᵐ t ∂μ, ((u.1 + c • v.1 : Lp ℝ 1 μ) : Ω → ℝ) t * g_c t =
        (u.1 : Ω → ℝ) t * g_c t + c * ((v.1 : Ω → ℝ) t * g_c t) := by
      filter_upwards [Lp.coeFn_add u.1 (c • v.1), Lp.coeFn_smul c v.1] with t h1 h2
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]; ring
    have h_eq : ∫ t, ((u.1 + c • v.1 : Lp ℝ 1 μ) : Ω → ℝ) t * g_c t ∂μ =
        ∫ t, (u.1 : Ω → ℝ) t * g_c t ∂μ + c * ∫ t, (v.1 : Ω → ℝ) t * g_c t ∂μ := by
      rw [integral_congr_ae h_ae, integral_add (h_int_prod u.1) ((h_int_prod v.1).const_mul c), integral_const_mul]
    rw [← h_eq]
    have h_norm_sum : ‖u.1 + c • v.1‖ = ∫ t, |((u.1 + c • v.1 : Lp ℝ 1 μ) : Ω → ℝ) t| ∂μ := by
      simpa [Real.norm_eq_abs] using L1.norm_eq_integral_norm (u.1 + c • v.1)
    rw [h_norm_sum]
    refine le_trans (integral_mono_ae (h_int_prod (u.1 + c • v.1)) (h_int_prod (u.1 + c • v.1)).abs
      (ae_of_all _ fun _ => le_abs_self _)) ?_
    refine integral_mono_ae (h_int_prod (u.1 + c • v.1)).abs (L1.integrable_coeFn (u.1 + c • v.1)).abs ?_
    filter_upwards [hgc_bound] with t ht
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) ht
  have h_disc_est : (∑' n, u.2 n * g_d n) + c * (∑' n, v.2 n * g_d n) ≤ ‖u.2 + c • v.2‖ := by
    have h_pt : ∀ n : ℕ, (u.2 + c • v.2) n * g_d n = u.2 n * g_d n + c * (v.2 n * g_d n) := by
      intro n
      have h_add : (u.2 + c • v.2) n = u.2 n + c * v.2 n := rfl
      rw [h_add]; ring
    have h_eq : (∑' n, (u.2 + c • v.2) n * g_d n) = (∑' n, u.2 n * g_d n) + c * (∑' n, v.2 n * g_d n) := by
      simp_rw [h_pt]
      rw [Summable.tsum_add (h_summ_prod u.2) ((h_summ_prod v.2).mul_left c), tsum_mul_left]
    rw [← h_eq, lp1_norm_eq_tsum_abs (u.2 + c • v.2)]
    have h_summ_sum := h_summ_prod (u.2 + c • v.2)
    have h_summ_abs := lp1_summable_abs (u.2 + c • v.2)
    calc ∑' n, (u.2 + c • v.2) n * g_d n
      _ ≤ ∑' n, |(u.2 + c • v.2) n * g_d n| :=
          Summable.tsum_le_tsum (fun n => le_abs_self _) h_summ_sum h_summ_sum.abs
      _ ≤ ∑' n, |(u.2 + c • v.2) n| :=
          Summable.tsum_le_tsum (fun n => by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hgd_bound n))
            h_summ_sum.abs h_summ_abs
  have h_ann := h_annihilate v hv
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  calc ‖u.1‖ + ‖u.2‖
    _ = (∫ t, (u.1 : Ω → ℝ) t * g_c t ∂μ) + (∑' n, u.2 n * g_d n) := by rw [h_norm_uc, h_norm_ud]
    _ = ((∫ t, (u.1 : Ω → ℝ) t * g_c t ∂μ) + c * ∫ t, (v.1 : Ω → ℝ) t * g_c t ∂μ) +
        ((∑' n, u.2 n * g_d n) + c * (∑' n, v.2 n * g_d n)) := by
        have : c * ((∫ t, (v.1 : Ω → ℝ) t * g_c t ∂μ) + (∑' n, v.2 n * g_d n)) = 0 := by rw [h_ann, mul_zero]
        linarith
    _ ≤ ‖u.1 + c • v.1‖ + ‖u.2 + c • v.2‖ := add_le_add h_cont_est h_disc_est

/-- ЗАМЕЧАНИЕ 1 (Формулы 8–9): Верификация предельного равенства баланса 1/2 ≤ 1/2
    для гибридного профиля v_c(t) = t - 1/2 на [0, 1] и v_d(n) = 2^{-(n+1)} (при n ≥ 0, т.е. 2^{-k} при k ≥ 1). -/
lemma remark1_hybrid_balance_check :

    |(∫ t in (0 : ℝ)..(1 : ℝ), (t - 1/2)) + (∑' k : ℕ, ((1/2 : ℝ) ^ (k + 2)))| = (1/2 : ℝ) := by
  have h_int : (∫ t in (0 : ℝ)..(1 : ℝ), (t - 1/2)) = 0 := by
    have h_id : IntervalIntegrable (fun t : ℝ => t) volume 0 1 := continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub h_id intervalIntegrable_const, intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    norm_num
  have h_sum : (∑' k : ℕ, ((1/2 : ℝ) ^ (k + 2))) = 1/2 := by
    have h_shift : (fun k : ℕ => ((1/2 : ℝ) ^ (k + 2))) = fun k : ℕ => (1/4 : ℝ) * ((1/2 : ℝ) ^ k) := by
      ext k; ring
    rw [h_shift, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [h_int, h_sum, zero_add]
  norm_num

end HybridSpaceTheory
/-! ### РАЗДЕЛЫ 3, 4 и 5: Квантование операторов (Теорема 2), NP-трудность (Теорема 3) и Конвейеры -/

section QuantizationAndComplexity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- ТЕОРЕМА 2 (О дискретизации и квантовании оператора, формула 11):
    ‖s_V(x) - s_{V,ε}(x_ε)‖ ≤ ‖I - Q‖ · ε + η(‖x‖ + ε) -/
theorem operator_quantization_error_bound
    (Q : X →L[ℝ] X) (s_quant : X → X)
    (ε η : ℝ) (_hε : 0 ≤ ε) (hη : 0 ≤ η)
    (h_quant : ∀ z : X, ‖(ContinuousLinearMap.id ℝ X - Q) z - s_quant z‖ ≤ η * ‖z‖)
    (x x_ε : X) (h_grid : ‖x - x_ε‖ ≤ ε) :
    ‖(ContinuousLinearMap.id ℝ X - Q) x - s_quant x_ε‖ ≤
      ‖ContinuousLinearMap.id ℝ X - Q‖ * ε + η * (‖x‖ + ε) := by
  let s_V := ContinuousLinearMap.id ℝ X - Q
  have h_tri : ‖s_V x - s_quant x_ε‖ ≤ ‖s_V x - s_V x_ε‖ + ‖s_V x_ε - s_quant x_ε‖ :=
    norm_sub_le_norm_sub_add_norm_sub (s_V x) (s_V x_ε) (s_quant x_ε)
  have h_disc : ‖s_V x - s_V x_ε‖ ≤ ‖s_V‖ * ε := by
    rw [← map_sub]
    calc ‖s_V (x - x_ε)‖ ≤ ‖s_V‖ * ‖x - x_ε‖ := s_V.le_opNorm (x - x_ε)
      _ ≤ ‖s_V‖ * ε := mul_le_mul_of_nonneg_left h_grid (norm_nonneg s_V)
  have h_norm_xε : ‖x_ε‖ ≤ ‖x‖ + ε := by
    have h1 : ‖x_ε‖ ≤ ‖x‖ + ‖x_ε - x‖ := norm_le_insert' x_ε x
    rw [norm_sub_rev] at h1
    linarith
  have h_round : ‖s_V x_ε - s_quant x_ε‖ ≤ η * (‖x‖ + ε) :=
    le_trans (h_quant x_ε) (mul_le_mul_of_nonneg_left h_norm_xε hη)
  exact le_trans h_tri (add_le_add h_disc h_round)

/-- РАЗДЕЛ 5 (Формула 18): Стабилизация вычислительных конвейеров при аддитивном шуме ‖δ‖ ≤ ε:
    ‖s_{V,ε}(x + δ) - s_{V,ε}(x)‖ ≤ ‖I - Q‖ · ε + η(2‖x‖ + ε) -/
theorem pipeline_perturbation_stability
    (Q : X →L[ℝ] X) (s_quant : X → X)
    (ε η : ℝ) (_hε : 0 ≤ ε) (hη : 0 ≤ η)
    (h_quant : ∀ z : X, ‖(ContinuousLinearMap.id ℝ X - Q) z - s_quant z‖ ≤ η * ‖z‖)
    (x δ : X) (hδ : ‖δ‖ ≤ ε) :
    ‖s_quant (x + δ) - s_quant x‖ ≤
      ‖ContinuousLinearMap.id ℝ X - Q‖ * ε + η * (2 * ‖x‖ + ε) := by
  let s_V := ContinuousLinearMap.id ℝ X - Q
  have h1 : ‖s_quant (x + δ) - s_quant x‖ ≤
      ‖s_quant (x + δ) - s_V (x + δ)‖ + ‖s_V (x + δ) - s_V x‖ + ‖s_V x - s_quant x‖ := by
    calc ‖s_quant (x + δ) - s_quant x‖
      _ ≤ ‖s_quant (x + δ) - s_V x‖ + ‖s_V x - s_quant x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ (s_V x) _
      _ ≤ (‖s_quant (x + δ) - s_V (x + δ)‖ + ‖s_V (x + δ) - s_V x‖) + ‖s_V x - s_quant x‖ := by
          gcongr
          exact norm_sub_le_norm_sub_add_norm_sub _ (s_V (x + δ)) _
  have h_q1 : ‖s_quant (x + δ) - s_V (x + δ)‖ ≤ η * (‖x‖ + ε) := by
    rw [norm_sub_rev]
    calc ‖s_V (x + δ) - s_quant (x + δ)‖ ≤ η * ‖x + δ‖ := h_quant (x + δ)
      _ ≤ η * (‖x‖ + ‖δ‖) := mul_le_mul_of_nonneg_left (norm_add_le x δ) hη
      _ ≤ η * (‖x‖ + ε) := mul_le_mul_of_nonneg_left (by linarith) hη
  have h_lip : ‖s_V (x + δ) - s_V x‖ ≤ ‖s_V‖ * ε := by
    rw [← map_sub, add_sub_cancel_left]
    calc ‖s_V δ‖ ≤ ‖s_V‖ * ‖δ‖ := s_V.le_opNorm δ
      _ ≤ ‖s_V‖ * ε := mul_le_mul_of_nonneg_left hδ (norm_nonneg s_V)
  have h_q2 : ‖s_V x - s_quant x‖ ≤ η * ‖x‖ := h_quant x
  linarith

/-- ТЕОРЕМА 3 (Часть 1 — Сведение Subset-Sum к булевым векторам на сдвинутой гиперплоскости V_T, формула 15):
    Существование подмножества I ⊆ Fin m с ∑_{i ∈ I} a_i = T (при T ≠ 0) эквивалентно
    существованию ненулевого булева вектора z : Fin m → {0, 1} на слое w(z) = T. -/
theorem subset_sum_iff_boolean_shifted_hyperplane {m : ℕ} (a : Fin m → ℤ) (T : ℤ) (hT : T ≠ 0) :
    (∃ I : Finset (Fin m), ∑ i ∈ I, a i = T) ↔
    (∃ z : Fin m → ℤ, (∀ i, z i = 0 ∨ z i = 1) ∧ z ≠ 0 ∧ ∑ i : Fin m, a i * z i = T) := by
  constructor
  · rintro ⟨I, hI⟩
    refine ⟨fun i => if i ∈ I then 1 else 0, fun i => by dsimp only; split_ifs <;> simp, ?_, ?_⟩
    · intro hz
      have h_zero : ∑ i ∈ I, a i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hzi : (if i ∈ I then (1 : ℤ) else 0) = 0 := congr_fun hz i
        simp [hi] at hzi
      rw [h_zero] at hI
      exact hT hI.symm
    · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
      exact hI
  · rintro ⟨z, hz_bool, _, h_sum⟩
    refine ⟨Finset.univ.filter (fun i => z i = 1), ?_⟩
    rw [← h_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases hz_bool i with h0 | h1
    · simp [h0]
    · simp [h1]

/-- ТЕОРЕМА 3 (Часть 2 — Сведение Partition к биполярным векторам в нулевом слое P_W⁻¹(0), формула 17):
    Для положительных весов a_i > 0 с ∑ a_i = 2S существование разбиения ∑_{i ∈ I} a_i = S
    эквивалентно существованию биполярного вектора u ∈ {-1, 1}^m с ортогональностью ∑ a_i u_i = 0. -/
theorem partition_iff_bipolar_null_layer {m : ℕ} (a : Fin m → ℤ) (S : ℤ)
    (h_total : ∑ i : Fin m, a i = 2 * S) :
    (∃ I : Finset (Fin m), ∑ i ∈ I, a i = S) ↔
    (∃ u : Fin m → ℤ, (∀ i, u i = 1 ∨ u i = -1) ∧ ∑ i : Fin m, a i * u i = 0) := by
  constructor
  · rintro ⟨I, hI⟩
    refine ⟨fun i => if i ∈ I then 1 else -1, fun i => by dsimp only; split_ifs <;> simp, ?_⟩
    have h_split : ∑ i : Fin m, a i = (∑ i ∈ I, a i) + (∑ i ∈ Finset.univ \ I, a i) := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_univ I)]
    have h_compl : ∑ i ∈ Finset.univ \ I, a i = S := by linarith
    have h_rewrite : ∑ i : Fin m, a i * (if i ∈ I then (1 : ℤ) else -1) =
        (∑ i ∈ I, a i) - (∑ i ∈ Finset.univ \ I, a i) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ I), add_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl; intro i hi; simp [hi]
      · apply Finset.sum_congr rfl; intro i hi
        have hni : i ∉ I := (Finset.mem_sdiff.mp hi).2
        simp [hni]
    rw [h_rewrite, hI, h_compl, sub_self]
  · rintro ⟨u, hu_bip, h_orth⟩
    refine ⟨Finset.univ.filter (fun i => u i = 1), ?_⟩
    have h_sum_u : ∑ i : Fin m, a i * u i =
        (∑ i ∈ Finset.univ.filter (fun i => u i = 1), a i) -
        (∑ i ∈ Finset.univ.filter (fun i => u i ≠ 1), a i) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => u i = 1) (fun i => a i * u i),
          sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl; intro i hi
        have h1 : u i = 1 := (Finset.mem_filter.mp hi).2
        simp [h1]
      · apply Finset.sum_congr rfl; intro i hi
        have hne : u i ≠ 1 := (Finset.mem_filter.mp hi).2
        rcases hu_bip i with h1 | hm1
        · exact False.elim (hne h1)
        · simp [hm1]
    have h_tot_split : ∑ i : Fin m, a i =
        (∑ i ∈ Finset.univ.filter (fun i => u i = 1), a i) +
        (∑ i ∈ Finset.univ.filter (fun i => u i ≠ 1), a i) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => u i = 1) a).symm
    linarith

end QuantizationAndComplexity
/-! ### ПРИЛОЖЕНИЕ Б: Матричный пример в ℓ₁⁸ (формулы 19–20) -/

section AppendixBL1_8

/-- Вектор весов A = (3, 5, -2, 7, 4, -1, 6, -3) из формулы (19) -/
def weights8 : Fin 8 → ℚ :=
  fun i => match i with
  | 0 => 3
  | 1 => 5
  | 2 => -2
  | 3 => 7
  | 4 => 4
  | 5 => -1
  | 6 => 6
  | 7 => -3

/-- Явная матрица линейного метрического селектора s_V = I - Q размерности 8×8 из формулы (20) -/
def selectorMatrix8 : Matrix (Fin 8) (Fin 8) ℚ :=
  Matrix.of fun i j =>
    if i = 3 then
      if j = 3 then 0 else -weights8 j / 7
    else
      if i = j then 1 else 0

/-- 1. Проверка идемпотентности проектора: s_V * s_V = s_V -/
lemma selectorMatrix8_idempotent :
    selectorMatrix8 * selectorMatrix8 = selectorMatrix8 := by
  ext i j
  fin_cases i
  all_goals
    fin_cases j
    all_goals
      simp [selectorMatrix8, weights8, Matrix.mul_apply, Fin.sum_univ_eight]
      

/-- 2. Проверка следа оператора: Tr(s_V) = 7 -/
lemma selectorMatrix8_trace :
    Matrix.trace selectorMatrix8 = 7 := by
  simp [Matrix.trace, selectorMatrix8, Fin.sum_univ_eight]
  norm_num

/-- 3. Проверка того, что образ s_V лежит в гиперплоскости V = ker w (то есть w^T * s_V = 0) -/
lemma selectorMatrix8_range_in_ker_w (j : Fin 8) :
    ∑ i : Fin 8, weights8 i * selectorMatrix8 i j = 0 := by
  fin_cases j
  all_goals
    simp [weights8, selectorMatrix8, Fin.sum_univ_eight]
    first | done | norm_num

/-- 4. Проверка того, что четвертый базисный вектор e_4 лежит в ядре ker s_V -/
lemma selectorMatrix8_ker_e4 :
    Matrix.mulVec selectorMatrix8 (Pi.single 3 1) = 0 := by
  ext i
  fin_cases i
  all_goals
    simp [selectorMatrix8, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- 5. Ортогональность ядра U = span{e_4} подпространству V = ker w в норме ℓ₁⁸:
    для любого c ∈ ℚ и v ∈ ker w выполнено |c| ≤ ∑_i |c·(e_4)_i - v_i| -/
lemma appendixB_birkhoff_orthogonality (c : ℚ) (v : Fin 8 → ℚ)
    (hv : ∑ i : Fin 8, weights8 i * v i = 0) :

    |c| ≤ ∑ i : Fin 8, |(if i = (3 : Fin 8) then c else 0) - v i| := by
  have h_sum_weights : 3 * v 0 + 5 * v 1 + -(2 * v 2) + 7 * v 3 + 4 * v 4 + -v 5 + 6 * v 6 + -(3 * v 7) = 0 := by
    simpa [weights8, Fin.sum_univ_eight] using hv
  have h_v3_bound : |v 3| ≤ |v 0| + |v 1| + |v 2| + |v 4| + |v 5| + |v 6| + |v 7| := by
    have h7 : 7 * |v 3| ≤ 7 * (|v 0| + |v 1| + |v 2| + |v 4| + |v 5| + |v 6| + |v 7|) := by
      have h_eq : 7 * v 3 = -(3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4 + -v 5 + 6 * v 6 + -(3 * v 7)) := by
        linarith
      have h_abs : 7 * |v 3| = |3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4 + -v 5 + 6 * v 6 + -(3 * v 7)| := by
        calc 7 * |v 3| = |7 * v 3| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 7)]
          _ = |-(3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4 + -v 5 + 6 * v 6 + -(3 * v 7))| := by rw [h_eq]
          _ = |3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4 + -v 5 + 6 * v 6 + -(3 * v 7)| := abs_neg _
      have h_tri : |3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4 + -v 5 + 6 * v 6 + -(3 * v 7)| ≤
          3 * |v 0| + 5 * |v 1| + 2 * |v 2| + 4 * |v 4| + |v 5| + 6 * |v 6| + 3 * |v 7| := by
        have t1 := abs_add_le (3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4 + -v 5 + 6 * v 6) (-(3 * v 7))
        have t2 := abs_add_le (3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4 + -v 5) (6 * v 6)
        have t3 := abs_add_le (3 * v 0 + 5 * v 1 + -(2 * v 2) + 4 * v 4) (-v 5)
        have t4 := abs_add_le (3 * v 0 + 5 * v 1 + -(2 * v 2)) (4 * v 4)
        have t5 := abs_add_le (3 * v 0 + 5 * v 1) (-(2 * v 2))
        have t6 := abs_add_le (3 * v 0) (5 * v 1)
        simp only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 2),
                   abs_of_pos (by norm_num : (0 : ℚ) < 3), abs_of_pos (by norm_num : (0 : ℚ) < 4),
                   abs_of_pos (by norm_num : (0 : ℚ) < 5), abs_of_pos (by norm_num : (0 : ℚ) < 6)]
          at t1 t2 t3 t4 t5 t6
        linarith
      have h_nonneg : 0 ≤ |v 0| ∧ 0 ≤ |v 1| ∧ 0 ≤ |v 2| ∧ 0 ≤ |v 4| ∧ 0 ≤ |v 5| ∧ 0 ≤ |v 6| ∧ 0 ≤ |v 7| :=
        ⟨abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _⟩
      linarith
    linarith
  have h_rhs : (∑ i : Fin 8, |(if i = (3 : Fin 8) then c else 0) - v i|) =

      |v 0| + |v 1| + |v 2| + |c - v 3| + |v 4| + |v 5| + |v 6| + |v 7| := by
    simp [Fin.sum_univ_eight]
  rw [h_rhs]
  have h_rev : |c| - |v 3| ≤ |c - v 3| := abs_sub_abs_le_abs_sub c (v 3)
  linarith

/-- 6. Точное вычисление операторной нормы (константы Липшица) в ℓ₁⁸:
    L = ‖s_V‖₁ = max_j ∑_i |(s_V)_{ij}| = 13 / 7 -/
lemma selectorMatrix8_l1_norm :
    ∀ j : Fin 8, (∑ i : Fin 8, |selectorMatrix8 i j|) ≤ 13 / 7 ∧
    (∑ i : Fin 8, |selectorMatrix8 i 6|) = 13 / 7 := by
  intro j
  refine ⟨?_, ?_⟩
  · fin_cases j
    all_goals
      simp [selectorMatrix8, weights8, Fin.sum_univ_eight]
      norm_num
  · simp [selectorMatrix8, weights8, Fin.sum_univ_eight]
    norm_num

end AppendixBL1_8

end HybridDiscretizationVerification
