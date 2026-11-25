// Lean compiler output
// Module: PureLean.Algebra
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section02_conj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section02_conj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section05_conj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section05_conj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section08_conj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section08_conj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section02_conj___redArg(lean_object* v_inst_1_, lean_object* v_g_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_mul_4_; lean_object* v_inv_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_mul_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_n(v_mul_4_, 2);
v_inv_5_ = lean_ctor_get(v_inst_1_, 2);
lean_inc(v_inv_5_);
lean_dec_ref(v_inst_1_);
lean_inc(v_g_2_);
v___x_6_ = lean_apply_2(v_mul_4_, v_g_2_, v_x_3_);
v___x_7_ = lean_apply_1(v_inv_5_, v_g_2_);
v___x_8_ = lean_apply_2(v_mul_4_, v___x_6_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section02_conj(lean_object* v_G_9_, lean_object* v_inst_10_, lean_object* v_g_11_, lean_object* v_x_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_purelean_PureLean_Algebra_Section02_conj___redArg(v_inst_10_, v_g_11_, v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow___redArg(lean_object* v_inst_14_, lean_object* v_a_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_zero_17_; uint8_t v_isZero_18_; 
v_zero_17_ = lean_unsigned_to_nat(0u);
v_isZero_18_ = lean_nat_dec_eq(v_x_16_, v_zero_17_);
if (v_isZero_18_ == 1)
{
lean_object* v_one_19_; 
lean_dec(v_a_15_);
v_one_19_ = lean_ctor_get(v_inst_14_, 1);
lean_inc(v_one_19_);
lean_dec_ref(v_inst_14_);
return v_one_19_;
}
else
{
lean_object* v_mul_20_; lean_object* v_one_21_; lean_object* v_n_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_mul_20_ = lean_ctor_get(v_inst_14_, 0);
lean_inc(v_mul_20_);
v_one_21_ = lean_unsigned_to_nat(1u);
v_n_22_ = lean_nat_sub(v_x_16_, v_one_21_);
lean_inc(v_a_15_);
v___x_23_ = lp_purelean_PureLean_Algebra_Section04_mpow___redArg(v_inst_14_, v_a_15_, v_n_22_);
lean_dec(v_n_22_);
v___x_24_ = lean_apply_2(v_mul_20_, v___x_23_, v_a_15_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow___redArg___boxed(lean_object* v_inst_25_, lean_object* v_a_26_, lean_object* v_x_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_purelean_PureLean_Algebra_Section04_mpow___redArg(v_inst_25_, v_a_26_, v_x_27_);
lean_dec(v_x_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow(lean_object* v_M_29_, lean_object* v_inst_30_, lean_object* v_a_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_purelean_PureLean_Algebra_Section04_mpow___redArg(v_inst_30_, v_a_31_, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section04_mpow___boxed(lean_object* v_M_34_, lean_object* v_inst_35_, lean_object* v_a_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_purelean_PureLean_Algebra_Section04_mpow(v_M_34_, v_inst_35_, v_a_36_, v_x_37_);
lean_dec(v_x_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section05_conj___redArg(lean_object* v_inst_39_, lean_object* v_g_40_, lean_object* v_x_41_){
_start:
{
lean_object* v_mul_42_; lean_object* v_inv_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_mul_42_ = lean_ctor_get(v_inst_39_, 0);
lean_inc_n(v_mul_42_, 2);
v_inv_43_ = lean_ctor_get(v_inst_39_, 2);
lean_inc(v_inv_43_);
lean_dec_ref(v_inst_39_);
lean_inc(v_g_40_);
v___x_44_ = lean_apply_2(v_mul_42_, v_g_40_, v_x_41_);
v___x_45_ = lean_apply_1(v_inv_43_, v_g_40_);
v___x_46_ = lean_apply_2(v_mul_42_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section05_conj(lean_object* v_G_47_, lean_object* v_inst_48_, lean_object* v_g_49_, lean_object* v_x_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_purelean_PureLean_Algebra_Section05_conj___redArg(v_inst_48_, v_g_49_, v_x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow___redArg(lean_object* v_inst_52_, lean_object* v_a_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_zero_55_; uint8_t v_isZero_56_; 
v_zero_55_ = lean_unsigned_to_nat(0u);
v_isZero_56_ = lean_nat_dec_eq(v_x_54_, v_zero_55_);
if (v_isZero_56_ == 1)
{
lean_object* v_one_57_; 
lean_dec(v_a_53_);
v_one_57_ = lean_ctor_get(v_inst_52_, 1);
lean_inc(v_one_57_);
lean_dec_ref(v_inst_52_);
return v_one_57_;
}
else
{
lean_object* v_mul_58_; lean_object* v_one_59_; lean_object* v_n_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_mul_58_ = lean_ctor_get(v_inst_52_, 0);
lean_inc(v_mul_58_);
v_one_59_ = lean_unsigned_to_nat(1u);
v_n_60_ = lean_nat_sub(v_x_54_, v_one_59_);
lean_inc(v_a_53_);
v___x_61_ = lp_purelean_PureLean_Algebra_Section07_mpow___redArg(v_inst_52_, v_a_53_, v_n_60_);
lean_dec(v_n_60_);
v___x_62_ = lean_apply_2(v_mul_58_, v___x_61_, v_a_53_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow___redArg___boxed(lean_object* v_inst_63_, lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_purelean_PureLean_Algebra_Section07_mpow___redArg(v_inst_63_, v_a_64_, v_x_65_);
lean_dec(v_x_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow(lean_object* v_M_67_, lean_object* v_inst_68_, lean_object* v_a_69_, lean_object* v_x_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_purelean_PureLean_Algebra_Section07_mpow___redArg(v_inst_68_, v_a_69_, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section07_mpow___boxed(lean_object* v_M_72_, lean_object* v_inst_73_, lean_object* v_a_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_purelean_PureLean_Algebra_Section07_mpow(v_M_72_, v_inst_73_, v_a_74_, v_x_75_);
lean_dec(v_x_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section08_conj___redArg(lean_object* v_inst_77_, lean_object* v_g_78_, lean_object* v_x_79_){
_start:
{
lean_object* v_mul_80_; lean_object* v_inv_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_mul_80_ = lean_ctor_get(v_inst_77_, 0);
lean_inc_n(v_mul_80_, 2);
v_inv_81_ = lean_ctor_get(v_inst_77_, 2);
lean_inc(v_inv_81_);
lean_dec_ref(v_inst_77_);
lean_inc(v_g_78_);
v___x_82_ = lean_apply_2(v_mul_80_, v_g_78_, v_x_79_);
v___x_83_ = lean_apply_1(v_inv_81_, v_g_78_);
v___x_84_ = lean_apply_2(v_mul_80_, v___x_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_Algebra_Section08_conj(lean_object* v_G_85_, lean_object* v_inst_86_, lean_object* v_g_87_, lean_object* v_x_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_purelean_PureLean_Algebra_Section08_conj___redArg(v_inst_86_, v_g_87_, v_x_88_);
return v___x_89_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_purelean_PureLean_Algebra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
