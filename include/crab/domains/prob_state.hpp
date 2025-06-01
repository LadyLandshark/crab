#ifndef PROB_STATE_DOMAIN_H
#define PROB_STATE_DOMAIN_H

#include <crab/types/reference_constraints.hpp>
#include <crab/types/variable.hpp>
#include <crab/types/tag.hpp>
#include <crab/domains/abstract_domain.hpp>
#include <crab/domains/abstract_domain_operators.hpp>
#include <crab/domains/abstract_domain_specialized_traits.hpp>
#include <crab/domains/backward_assign_operations.hpp>
#include <crab/domains/interval.hpp>
#include <crab/domains/linear_interval_solver.hpp>
#include <crab/domains/separate_domains.hpp>
#include <crab/support/stats.hpp>

#include "ProbabilityState.h"
#include "Distribution.h"
#include "prob_hybrid.hpp"

#define MAX_REDUCTION_CYCLES 100

namespace ikos {

template<typename Number, typename VariableName>
class prob_state_domain final: public
	crab::domains::abstract_domain_api<prob_state_domain<Number, VariableName> >
{
public:
	using prob_state_domain_t = prob_state_domain<Number, VariableName>;
	using abstract_domain_t =
	  crab::domains::abstract_domain_api<prob_state_domain_t>;
	using typename abstract_domain_t::disjunctive_linear_constraint_system_t;
	using typename abstract_domain_t::interval_t;
	using typename abstract_domain_t::linear_constraint_system_t;
	using typename abstract_domain_t::linear_constraint_t;
	using typename abstract_domain_t::linear_expression_t;
	using typename abstract_domain_t::reference_constraint_t;
	using typename abstract_domain_t::variable_or_constant_t;
	using typename abstract_domain_t::variable_or_constant_vector_t;
	using typename abstract_domain_t::variable_t;
	using typename abstract_domain_t::variable_vector_t;
	//using constant_t = constant<Number>;
	using number_t = Number;
	using varname_t = VariableName;

private:
	using separate_domain_t = separate_domain<variable_t, interval_t>;
	using solver_t = linear_interval_solver<number_t, varname_t, separate_domain_t>;

public:
  using iterator = typename separate_domain_t::iterator;
	
private:
	ProbInvlSetDomain<number_t, varname_t> prob_state;

	prob_state_domain(separate_domain_t env, ProbabilityState prob_s)
	{
		ProbInvlSetDomain<number_t, varname_t> prob_state(env, prob_s);
		this->prob_state = prob_state;
	}
	
	//prob_state_domain(separate_domain_t env, ProbabilityState prob_s)
	//{
	//	this->env = env;
	//	this->prob_state = prob_s;
	//}

	//prob_state_domain()
	//{
	//	this->env = separate_domain_t();
	//	this->prob_state = ProbabilityState();	
	//}


	interval_t operator[](linear_expression_t expr) 
	{
		interval_t r(expr.constant());
		for (typename linear_expression_t::const_iterator it = expr.begin();
				 it != expr.end(); ++it) 
		{
			interval_t c(it->first);
			r += c * this->prob_state.at(it->second);
		}
		return r;
	}

	void add(const linear_constraint_system_t &csts,
			std::size_t threshold = MAX_REDUCTION_CYCLES) 
	{
		if (!this->is_bottom())
		{
			linear_constraint_system_t pp_csts;
			for (auto const &c : csts) 
			{
				if (c.is_disequation())
				{
					// We try to convert a disequation into a strict inequality
					crab::domains::constraint_simp_domain_traits<prob_state_domain_t>::
						lower_disequality(*this, c, pp_csts);
				}
				pp_csts += c;
			}
			solver_t solver(pp_csts, threshold);
			auto reduced = this->prob_state.get_reduced_set();
			solver.run(reduced[0].first);
		}
	}

	prob_state_domain_t operator+(const linear_constraint_system_t &csts) 
	{
		prob_state_domain_t e(this);
		e += csts;
		return e;
	}

public:

	prob_state_domain() : prob_state(ProbInvlSetDomain<number_t, varname_t>::bottom()) {}

	prob_state_domain(const prob_state_domain_t &other) : prob_state(other.prob_state) {}

	prob_state_domain(const ProbInvlSetDomain<number_t, varname_t> &other_state) : prob_state(other_state) {}

	prob_state_domain_t &operator=(const prob_state_domain_t &o) 
	{
		if(this != &o)
		{
			this->prob_state = o.prob_state;
		}
		return *this;
	}	

	iterator begin() { return this->prob_state.get_dom_set().begin(); }
	iterator end() { return this->prob_state.get_dom_set().end(); }

	// Lattice operations
	prob_state_domain_t make_bottom() const override
	{
		return prob_state_domain_t(separate_domain_t::bottom(), ProbabilityState::bottom());
	}


	prob_state_domain_t make_top() const override
	{
		//CRAB_WARN("Make top");
		return prob_state_domain_t(separate_domain_t::top(), ProbabilityState::top());
	}

	void set_to_top() override 
	{
		//CRAB_WARN("Set to top", this->prob_state.to_string());
		//CRAB_WARN("{\"Set to top\": ", this->prob_state.to_string(), "}");
		this->prob_state = ProbInvlSetDomain<number_t, varname_t>::top();
		//CRAB_WARN("{\"Set to top (after)\": ", this->prob_state.to_string(), "}");
	}

	void set_to_bottom() override 
	{
		//CRAB_WARN("{\"Set to bottom\": ", this->prob_state.to_string(), "}");
		this->prob_state = ProbInvlSetDomain<number_t, varname_t>::top();
	}

	bool is_bottom() const override
	{
		//CRAB_WARN("{\"Is bottom\": ", this->prob_state.is_bottom(), "}");
		return prob_state.is_bottom();
	}

	bool is_top() const override
	{
		//CRAB_WARN("{\"Is top\": ", this->prob_state.is_top(), "}");
		return prob_state.is_top();
	}

	// Inclusion operator: return true if *this is equal or more precise than abs
	bool operator<=(const prob_state_domain_t &o) const override
	{
		CRAB_WARN("{\"Compare (<=)\": {\"this\": ", this->prob_state.to_string(), ", \"other\": ", o.prob_state.to_string(), "}}");
		crab::CrabStats::count(domain_name() + ".count.leq");
		crab::ScopedCrabStats __st__(domain_name() + ".leq");
		return this->prob_state <= o.prob_state;
	}

	// Join operator: return join(*this, abs)
	prob_state_domain_t operator|(const prob_state_domain_t &abs) const override
	{
		//CRAB_WARN("Join (op)");
		CRAB_WARN("{\"Join (op)\": {\"this\": ", this->prob_state.to_string(), ", \"other\": ", abs.prob_state.to_string(), "}}");
		CRAB_WARN("{\"Join (after)\": ", (this->prob_state | abs.prob_state).to_string(), "}");
		return prob_state_domain(this->prob_state | abs.prob_state);
	}
	// *this = join(*this, abs)
	void operator|=(const prob_state_domain_t &abs) override
	{
		//CRAB_WARN("Join eq (op)");
		CRAB_WARN("{\"Join eq (op)\": {\"this\": ", this->prob_state.to_string(), ", \"other\": ", abs.prob_state.to_string(), "}}");
		this->prob_state.join(abs.prob_state);
		CRAB_WARN("{\"Join eq (after)\": ", this->prob_state.to_string(), "}");
	}

	// *this = meet(*this, abs)
	void operator&=(const prob_state_domain_t &abs) override
	{
		//CRAB_WARN("Meet eq (op)");
		CRAB_WARN("{\"Meet eq (op)\": {\"this\": ", this->prob_state.to_string(), ", \"other\": ", abs.prob_state.to_string(), "}}");
		this->prob_state.meet(abs.prob_state);
	}
		
	// Meet operator: return meet(*this, abs)
	prob_state_domain_t operator&(const prob_state_domain_t &abs) const override
	{
		//CRAB_WARN("Meet (op)");
		CRAB_WARN("{\"Meet (op)\": {\"this\": ", this->prob_state.to_string(), ", \"other\": ", abs.prob_state.to_string(), "}}");
		return prob_state_domain(this->prob_state & abs.prob_state);
	}
	// Widening operator: return widening(*this, abs)
	prob_state_domain_t operator||(const prob_state_domain_t &abs) const override
	{
		//CRAB_WARN("Widening (op)");
		CRAB_WARN("{\"Widening (op)\": {\"this\": ", this->prob_state.to_string(), ", \"other\": ", abs.prob_state.to_string(), "}}");
		CRAB_WARN("{\"Widening (after)\": ", (this->prob_state || abs.prob_state).to_string(), "}");
		return prob_state_domain(this->prob_state || abs.prob_state);
	}

	// Narrowing operator: return narrowing(*this, abs)
	prob_state_domain_t operator&&(const prob_state_domain_t &abs) const override
	{
		//CRAB_WARN("Narrowing (op)");
		CRAB_WARN("{\"Narrowing (op)\": {\"this\": ", this->prob_state.to_string(), ", \"other\": ", abs.prob_state.to_string(), "}}");
		CRAB_WARN("{\"Narrowing (after)\": ", (this->prob_state && abs.prob_state).to_string(), "}");
		return prob_state_domain(this->prob_state && abs.prob_state);
	}
	// Widening with thresholds: return widening(*this, abs) using thresholds ts
	prob_state_domain_t widening_thresholds(
		const prob_state_domain_t &abs,
		const crab::thresholds<number_t> &ts) const override
	{
		//prob_state.widen_with(abs.prob_state, ts);
		return prob_state_domain(this->prob_state || abs.prob_state);
	}

	void set(const variable_t &v, interval_t i) {
		this->prob_state.set(v, i);
	}

	void set(const variable_t &v, number_t n) {
		this->prob_state.set(v, interval_t(n));
	}

	void set(const variable_t &v, std::vector<interval_t> ivec)
	{
		this->prob_state.set(v, ivec);
	}

	// add all constraints \in csts
	void operator+=(const linear_constraint_system_t &csts) override {
		this->add(csts);
	}
	
	// return true only if *this entails rhs
	virtual bool entails(const linear_constraint_t &cst) const override {	
		if(is_bottom()) 							
		   return true;							
		if(cst.is_tautology())
		   return true;							
		if(cst.is_contradiction())
			return false;							
		return false;
	}

	/**************************** Numerical operations *************************/
	// x := y op z
	void apply(crab::domains::arith_operation_t op, const variable_t &x,
					 const variable_t &y, const variable_t &z) override
	{
		//CRAB_WARN("Apply arith y op z");
		//CRAB_WARN("Apply arith y op z: ", this->prob_state.to_string());
		CRAB_WARN("{\"Apply arith y op z\": ", this->prob_state.to_string(), "}");
		interval_t yi = this->prob_state.at(y);
		interval_t zi = this->prob_state.at(z);
		interval_t xi = interval_t::bottom();

		switch (op) {
		case crab::domains::OP_ADDITION:
			xi = yi + zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_SUBTRACTION:
			xi = yi - zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_MULTIPLICATION:
			xi = yi * zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_SDIV:
			xi = yi / zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_UDIV:
			xi = yi.UDiv(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_SREM:
			this->prob_state.sample(Distribution::uniform(0, 2));
			xi = yi.SRem(zi);
			break;
		default:
			//case crab::domains::OP_UREM:
			xi = yi.URem(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		this->prob_state.set(x, xi);
		prob_state.reduce_rvs();
	}

	// x := y op k
	void apply(crab::domains::arith_operation_t op, const variable_t &x,
		 const variable_t &y, number_t k) override
	{
		//CRAB_WARN("Apply arith y op k");
		//CRAB_WARN("Apply arith y op k: ", this->prob_state.to_string());
		CRAB_WARN("{\"Apply arith y op k\": ", this->prob_state.to_string(), "}");
		interval_t yi = this->prob_state.at(y);
		interval_t xi = interval_t::bottom();
		interval_t zi(k);

		switch (op) {
		case crab::domains::OP_ADDITION:
			xi = yi + zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_SUBTRACTION:
			xi = yi - zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_MULTIPLICATION:
			xi = yi * zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_SDIV:
			xi = yi / zi;
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_UDIV:
			xi = yi.UDiv(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		case crab::domains::OP_SREM:
			xi = yi.SRem(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		default:
			//case crab::domains::OP_UREM:
			xi = yi.URem(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}

		this->prob_state.set(x, xi);
		prob_state.reduce_rvs();
	}

	// bitwise operations
	void apply(crab::domains::bitwise_operation_t op, const variable_t &x,
			 const variable_t &y, const variable_t &z) override 
	{
		//CRAB_WARN("Apply bitwise y op z");
		//CRAB_WARN("Apply bitwise y op z: ", this->prob_state.to_string());
		CRAB_WARN("{\"Apply bitwise y op z\": ", this->prob_state.to_string(), "}");
		interval_t yi = this->prob_state.at(y);
		interval_t zi = this->prob_state.at(z);
		interval_t xi = interval_t::bottom();

		switch (op) {
		case crab::domains::OP_AND: {
			xi = yi.And(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_OR: {
			xi = yi.Or(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_XOR: {
			xi = yi.Xor(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_SHL: {
			xi = yi.Shl(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_LSHR: {
			xi = yi.LShr(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		default:
			//case crab::domains::OP_ASHR:
			xi = yi.AShr(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}

		this->prob_state.set(x, xi);
		this->prob_state.reduce_rvs();
	}

	void apply(crab::domains::bitwise_operation_t op, const variable_t &x,
			 const variable_t &y, number_t k) override 
	{
		//CRAB_WARN("Apply bitwise y op k");
		//CRAB_WARN("Apply bitwise y op k: ", this->prob_state.to_string());
		CRAB_WARN("{\"Apply bitwise y op k\": ", this->prob_state.to_string(), "}");
		interval_t yi = this->prob_state.at(y);
		interval_t xi = interval_t::bottom();
		interval_t zi(k);

		switch (op) {
		case crab::domains::OP_AND: {
			xi = yi.And(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_OR: {
			xi = yi.Or(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_XOR: {
			xi = yi.Xor(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_SHL: {
			xi = yi.Shl(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		case crab::domains::OP_LSHR: {
			xi = yi.LShr(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		default:
			//case crab::domains::OP_ASHR: 
			xi = yi.AShr(zi);
			this->prob_state.sample(Distribution::uniform(0, 2));
			break;
		}
		
		this->prob_state.set(x, xi);
		this->prob_state.reduce_rvs();
	}
	
	// x := e
	void assign(const variable_t &x, const linear_expression_t &e) override
	{
		//CRAB_WARN("Assign (op)");
		//CRAB_WARN("Assign op: ", this->prob_state.to_string());
		//CRAB_WARN("{\"Assign op\": ", this->prob_state.to_string(), "}");
		if(boost::optional<variable_t> v = e.get_variable())
			this->prob_state.set(x, this->prob_state.at(*v));
		else 
		{
			interval_t r = e.constant();
			for(auto kv : e)
			{
				r += kv.first * this->prob_state.at(kv.second);
			}
			this->prob_state.set(x, r);
		}
		prob_state.sample(Distribution::uniform(0, 2));
		prob_state.reduce_rvs();
		//CRAB_WARN("{\"Assign op (after)\": ", this->prob_state.to_string(), "}");
	}

	// join(*this, copy_of_this(x := e))
	void weak_assign(const variable_t &x, const linear_expression_t &e) override
	{
		//CRAB_WARN("Weak assign");
		//CRAB_WARN("Weak Assign op: ", this->prob_state.to_string());
		CRAB_WARN("{\"Weak Assign op\": ", this->prob_state.to_string(), "}");
		if (boost::optional<variable_t> v = e.get_variable())
			this->prob_state.invl_bcast_join(x, this->prob_state.at(*v));
		else 
		{
			interval_t r = e.constant();
			for (auto kv : e) 
			{
				r += kv.first * this->prob_state.at(kv.second);
			}
			this->prob_state.invl_bcast_join(x, r);
		}
		prob_state.sample(Distribution::uniform(0, 2));
		prob_state.reduce_rvs();
	}


	// dst := src
	void apply(crab::domains::int_conv_operation_t op, const variable_t &dst,
		const variable_t &src) override
	{
		//CRAB_WARN("Apply (dest := src)", this->prob_state.to_string());
		CRAB_WARN("{\"Apply (dest := src)\": ", this->prob_state.to_string(), "}");
		crab::domains::int_cast_domain_traits<prob_state_domain_t>::apply(*this, op, dst, src);
	}


	// if(cond) lhs := e1 else lhs := e2
	void select(const variable_t &lhs, const linear_constraint_t &cond,
			  const linear_expression_t &e1,  const linear_expression_t &e2) override
	{
		//CRAB_WARN("Select");
		CRAB_WARN("Select: ", this->prob_state.to_string());
		if (!is_bottom()) 
		{
			prob_state_domain_t inv1(*this);
			inv1 += cond;	
			if (inv1.is_bottom()) 
			{
				assign(lhs, e2);
				return;
			}
			inv1.prob_state.sample(Distribution::uniform(0, 2));
			inv1.prob_state.reduce_rvs();
			
			prob_state_domain_t inv2(*this);
			inv2 += cond.negate();
			if (inv2.is_bottom()) 
			{
				assign(lhs, e1);
				return;
			}
			inv2.prob_state.sample(Distribution::uniform(0, 2));
			inv2.prob_state.reduce_rvs();

			this->prob_state = inv1.prob_state | inv2.prob_state;
			
			auto first_invl = this->operator[](e1);
			auto second_invl = this->operator[](e2);	


			set(lhs, first_invl | second_invl);
		}
	}


	/// prob_state_domain_t implements only standard abstract operations of
	/// a numerical domain so it is intended to be used as a leaf domain
	/// in the hierarchy of domains.
	BOOL_OPERATIONS_NOT_IMPLEMENTED(prob_state_domain_t)
	ARRAY_OPERATIONS_NOT_IMPLEMENTED(prob_state_domain_t)
	REGION_AND_REFERENCE_OPERATIONS_NOT_IMPLEMENTED(prob_state_domain_t)
	/**************************** Miscellaneous operations ****************/
	// Forget v
	void operator-=(const variable_t &v) override
	{
		if (!is_bottom()) {
			this->prob_state -= v;
		}
	}

	// Return an interval with the possible values of v if such notion
	// exists in the abstract domain. Calling this method might trigger
	// normalization if the underlying domain requires so.
	interval_t operator[](const variable_t &v) override
	{
		return at(v);
	}

	// Similar to operator[] but it doesn't modify the internal state.
	interval_t at(const variable_t &v) const override
	{
		return this->prob_state.at(v);
	}

	// Convert the abstract state into a conjunction of linear constraints.
	linear_constraint_system_t to_linear_constraint_system() const override
	{
		linear_constraint_system_t csts;

		if (this->is_bottom()) 
		{
			csts += linear_constraint_t::get_false();
		}
		return csts;
	}

	// Convert the abstract state into a disjunction of conjunction
	// of linear constraints.
	disjunctive_linear_constraint_system_t
		to_disjunctive_linear_constraint_system() const override
	{
		auto lin_csts = to_linear_constraint_system();
		if (lin_csts.is_false())
			return disjunctive_linear_constraint_system_t(true /*is_false*/);
		else if (lin_csts.is_true())
			return disjunctive_linear_constraint_system_t(false /*is_false*/);
		else
			return disjunctive_linear_constraint_system_t(lin_csts);
	}

	// Rename in the abstract state the variables "from" with those from to.
	//
	// If any variable from "to" exists already in the abstract state
	// then an error will be raised. This might be a bit restrictive and
	// it can be relaxed if needed in the future.
	void rename(const variable_vector_t &from,
					  const variable_vector_t &to) override
	{
		this->prob_state.rename(from, to);
	}

	// Normalize the abstract domain if such notion exists.
	void normalize() override {}

	// Reduce the size of the abstract domain representation.
	void minimize() override {}

	// Forget variables form the abstract domain
	void forget(const variable_vector_t &variables) override
	{
		if(is_bottom() || is_top())
		  return;
		for (auto const &var : variables) 
		  this->operator-=(var);
	}

	// Project the abstract domain onto variables (dual to forget)
	void project(const variable_vector_t &variables) override
	{
		this->prob_state.project(variables);
	}

	// Make a new copy of var without relating var with new_var
	void expand(const variable_t &var, const variable_t &new_var) override
	{
		if (is_bottom() || is_top())
			return;

		set(new_var, this->prob_state.at(var));
	}


	// Function whose semantics is defined by the particular abstract
	// domain
	void intrinsic(std::string name,
			 const variable_or_constant_vector_t &inputs,
						 const variable_vector_t &outputs) override
	{
		CRAB_WARN("Intrinsics ", name, " not implemented by ", domain_name());
	}

	void backward_intrinsic(std::string name,
								  const variable_or_constant_vector_t &inputs,
								  const variable_vector_t &outputs,
								  const prob_state_domain_t &invariant) override
	{
		CRAB_WARN("Intrinsics ", name, " not implemented by ", domain_name());
	}

	void backward_apply(crab::domains::arith_operation_t op, const variable_t &x,
			const variable_t &y, number_t z, const prob_state_domain_t &inv) override 
	{
		crab::domains::BackwardAssignOps<prob_state_domain_t>::apply(*this, op, x, y, z, inv);
	}

	void backward_apply(crab::domains::arith_operation_t op, const variable_t &x,
			const variable_t &y, const variable_t &z, const prob_state_domain_t &inv) override 
	{
		crab::domains::BackwardAssignOps<prob_state_domain_t>::apply(*this, op, x, y, z, inv);
	}
	
	void backward_assign(const variable_t &x, 
			const linear_expression_t &e, const prob_state_domain_t &inv) override 
	{
		crab::domains::BackwardAssignOps<prob_state_domain_t>::assign(*this, x, e, inv);
	}

	// Print the internal state of the abstract domain
	void write(crab::crab_os &o) const override
	{
		this->prob_state.write(o);
	}


	//std::string write() const
	//{
	//	return this->prob_state.to_string();
	//}

	// Return a string the abstract domain name
	std::string domain_name(void) const override { return "Probability State"; }

	ProbabilityState get_prob_state() { return this->prob_state; }

	//friend crab::crab_os &operator<<(crab::crab_os &o,
	//							   const abstract_domain_api<prob_state_domain> &dom)
	//{
	//	dom.write(o);
	//	return o;
	//}

};
} // namespace ikos

namespace crab {
namespace domains {
template<typename Number, typename VariableName>
struct abstract_domain_traits<ikos::prob_state_domain<Number, VariableName> >
{
	using number_t = Number;
	using varname_t = VariableName;
};
}// namespace domains
}// namespace crab

#endif /* PROB_STATE_DOMAIN_H */

