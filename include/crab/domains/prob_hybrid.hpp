#ifndef PROB_HYBRID_H
#define PROB_HYBRID_H

#endif /* PROB_HYBRID_H */

#include <vector>
#include <algorithm>
#include <utility>
#include <iostream>

#include <crab/types/variable.hpp>
#include <crab/domains/abstract_domain.hpp>
#include <crab/domains/abstract_domain_specialized_traits.hpp>
#include <crab/domains/backward_assign_operations.hpp>
#include <crab/domains/interval.hpp>
#include <crab/domains/linear_interval_solver.hpp>
#include <crab/domains/separate_domains.hpp>

#include "ProbabilityState.h"

#define JOIN_THRESHOLD 100000

namespace ikos {

template <typename Number, typename VariableName>
class ProbInvlSetDomain{
	public:
		using number_t = Number;
		using varname_t = VariableName;
		using variable_t = crab::variable<number_t, varname_t>;
		using interval_t = interval<number_t>;
	   	using invl_dom_t = separate_domain<variable_t, interval_t>;
		using prob_state_t = ProbabilityState;
		using dom_pair_t = std::pair<invl_dom_t, prob_state_t>;
		using dom_set_t = std::vector<dom_pair_t>;
		using var_vec_t = std::vector<variable_t>;
		using invl_vec_t = std::vector<interval_t>;
		using dom_iter_t = typename dom_set_t::iterator;
		using prob_invl_set_dom_t = ProbInvlSetDomain<number_t, varname_t>;

	private:
		dom_set_t dom_set;
	
	public:
		ProbInvlSetDomain() 
		{
			this->dom_set = dom_set_t();
			//this->dom_set.push_back(std::make_pair(invl_dom_t::bottom(), prob_state_t::bottom()));
		}

		dom_set_t get_dom_set() const { return this->dom_set; }

		ProbInvlSetDomain(const ProbInvlSetDomain &other) : dom_set(other.dom_set) {}

		ProbInvlSetDomain(dom_set_t dom_set) : dom_set(dom_set) {}

		ProbInvlSetDomain(dom_pair_t dom_pair)
		{
			this->dom_set = ProbInvlSetDomain<Number, VariableName>::dom_set_t();
			this->dom_set.push_back(dom_pair);
		}

		ProbInvlSetDomain(invl_dom_t invl_dom, prob_state_t prob_state)
		{
			this->dom_set = ProbInvlSetDomain<Number, VariableName>::dom_set_t();
			auto dom_pair = std::make_pair(invl_dom, prob_state);
			this->dom_set.push_back(dom_pair);
		}

		static bool doms_eq(dom_pair_t const & a, dom_pair_t const & b)
		{
			bool invl_eq = a.first == b.first;
			bool prob_state_eq = a.second == b.second;
			return invl_eq && prob_state_eq;
		}

		static bool doms_lt(dom_pair_t const & a, dom_pair_t const & b)
		{
			// Strict weak ordering for set operations
			//std::cerr << "Doms_lt\n\ta: " << a.second.to_string() << "\n\tb: " << b.second.to_string() << std::endl;
			bool is_lt = (!a.first.is_top() && b.first.is_top()) || 
								(!b.first.is_top() && !a.first.is_top() && a.first.size() < b.first.size());
			
			bool same_size = (a.first.is_top() && b.first.is_top()) || 
								(!a.first.is_top() && !b.first.is_top() && (a.first.size() == b.first.size()));

			if(same_size && !ProbInvlSetDomain::doms_eq(a, b))
			{

				bool invl_lt = (a.first <= b.first) && !(a.first == b.first);
				//std::cerr << "Interval a <= b: " <<  (a.first <= b.first) << std::endl;
				//std::cerr << "Interval a != b: " <<  !(a.first == b.first) << std::endl;
				//std::cerr << "Interval b <= a: " <<  (b.first <= a.first) << std::endl;
				bool prob_state_lt = (a.second <= b.second) && !(a.second == b.second);
				//std::cerr << "Prob State a <= b: " << (a.second <= b.second) << std::endl;
				//std::cerr << "Prob State a != b: " << !(a.second == b.second) << std::endl;
				//std::cerr << "Prob State b <= a: " << (b.second <= a.second) << std::endl;
				//std::cerr << "Invl lt || Prob_state_lt: " << (invl_lt || prob_state_lt) << std::endl;
				is_lt = invl_lt && prob_state_lt;
			}
			return is_lt;
		}

		static dom_set_t dedup(dom_set_t dom_set)
		{
			dom_set_t temp = dom_set_t();
			std::sort(dom_set.begin(), dom_set.end(), ProbInvlSetDomain::doms_lt);

			for(int i = 0; i < dom_set.size(); i++)
			{
				bool dup_found = false;
				for(int j = i+1; j < dom_set.size(); j++)
				{
					if(ProbInvlSetDomain::doms_eq(dom_set[i], dom_set[j]))
						dup_found = true;
				}
				if(!dup_found)
					temp.push_back(dom_set[i]);
			}
			return temp;
		}


		void add_dom_pair(invl_dom_t invl, prob_state_t prob_state)
		{
			auto dom_pair = std::make_pair(invl, prob_state);
			this->dom_set.push_back(dom_pair);
		}

		static ProbInvlSetDomain top()
		{
			prob_invl_set_dom_t temp = ProbInvlSetDomain();
			temp.add_dom_pair(invl_dom_t::top(), prob_state_t::top());
			return temp;
		}

		static ProbInvlSetDomain bottom()
		{
			prob_invl_set_dom_t temp = ProbInvlSetDomain();
			temp.add_dom_pair(invl_dom_t::bottom(), prob_state_t::bottom());
			return temp;
		}

		void set_to_bottom()
		{
			this->dom_set.clear();
			this->add_dom_pair(invl_dom_t::bottom(), prob_state_t::bottom());
		}

		void set_to_top()
		{
			this->dom_set.clear();
			this->add_dom_pair(invl_dom_t::top(), prob_state_t::top());
		}

		bool is_top() const
		{
			for(auto elem : this->dom_set)
			{
				if(elem.first.is_top() && elem.second.is_top())
					return true;
			}
			return false;
		}

		size_t length() const
		{
			return this->dom_set.size();
		}

		bool is_bottom() const
		{
			for(auto elem : this->dom_set)
			{
				if(!elem.first.is_bottom() || !elem.second.is_bottom())
					return false;
			}
			return true;
		}
	
		dom_set_t get_reduced_set()
		{
			dom_set_t reduced = dom_set_t();
			dom_pair_t new_pair;

			auto prob_iter = this->dom_set.begin();
			new_pair.first = prob_iter->first;
			new_pair.second = prob_iter->second;
			prob_iter++;

			for(auto iter = prob_iter; iter != this->dom_set.end(); iter++)
			{
				new_pair.first = new_pair.first | iter->first;
				new_pair.second = new_pair.second | iter->second;
			}
			reduced.push_back(new_pair);
			return reduced;
		}

		void reduce_set()
		{
			dom_set_t reduced = this->get_reduced_set();
			//this->dom_set.clear();
			this->dom_set = reduced;
		}

		bool operator<=(const ProbInvlSetDomain &other) const
		{
			if(this->is_bottom())
				return true;
			if(other.is_bottom())
				return false;

			//prob_invl_set_dom_t temp_this = prob_invl_set_dom_t(*this);
			//prob_invl_set_dom_t temp_other = prob_invl_set_dom_t(other);

			//dom_set_t this_set = temp_this.get_reduced_set();
			//dom_set_t other_set = temp_other.get_reduced_set();
			//
			//return (this_set[0].first <= other_set[0].first) && (this_set[0].second <= other_set[0].second);
			
			auto other_set = other.get_dom_set();
			auto this_set = this->get_dom_set();
			bool top_flag = false;
			for(auto this_elem : this_set)
			{
				bool in_flag = false;
				for(auto other_elem : other_set)
				{
					if((this_elem.first <= other_elem.first) 
							&& (this_elem.second <= other_elem.second))
						in_flag = true;
					
				}
				top_flag = in_flag;
			}
			return top_flag;
		}

		void invl_bcast_join(const variable_t &x, interval_t invl)
		{
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->first.join(x, invl);
			}
		}

		void join(const ProbInvlSetDomain &other)
		{
			dom_set_t joined = dom_set_t();
			dom_set_t other_dom_set = other.get_dom_set();
			dom_set_t this_dom_set = this->get_dom_set();

			//this_dom_set.insert(this_dom_set.end(), other_dom_set.begin(), other_dom_set.end());
			//joined = ProbInvlSetDomain::dedup(this_dom_set);
			
			//joined = this_dom_set | other_dom_set;
			
			std::sort(this_dom_set.begin(), this_dom_set.end(), ProbInvlSetDomain::doms_lt);
			std::sort(other_dom_set.begin(), other_dom_set.end(), ProbInvlSetDomain::doms_lt);
			std::set_union(this_dom_set.begin(), this_dom_set.end(),
					other_dom_set.begin(), other_dom_set.end(),
					std::back_inserter(joined), ProbInvlSetDomain::doms_lt);
					

			//std::cerr << "Joined length: " << joined.size() << std::endl;
			this->dom_set.clear();
			this->dom_set = joined;
			if(joined.size() >= JOIN_THRESHOLD)
				this->reduce_set();
		}

		ProbInvlSetDomain operator|(const ProbInvlSetDomain &other) const
		{
			if(this->is_bottom())
				return other;
			else if(other.is_bottom())
				return *this;
			else
			{
				prob_invl_set_dom_t temp = ProbInvlSetDomain(*this);
				temp.join(other);
				return temp;
			}
		}

		void meet(const ProbInvlSetDomain &other)
		{
			dom_set_t other_dom_set = other.get_dom_set();
			dom_set_t this_dom_set = this->get_dom_set();
			size_t len = std::max(this->dom_set.size(), other_dom_set.size());
			dom_set_t met = dom_set_t();

			//std::sort(this_set.begin(), this_set.end(), ProbInvlSetDomain::doms_lt);
			//std::sort(other_dom_set.begin(), other_dom_set.end(), ProbInvlSetDomain::doms_lt);

			//met = this_set & other_dom_set;

			std::sort(this_dom_set.begin(), this_dom_set.end(), ProbInvlSetDomain::doms_lt);
			std::sort(other_dom_set.begin(), other_dom_set.end(), ProbInvlSetDomain::doms_lt);
			std::set_intersection(this_dom_set.begin(), this_dom_set.end(),
					other_dom_set.begin(), other_dom_set.end(),
					std::back_inserter(met), ProbInvlSetDomain::doms_lt);
			
			//for(int i = 0; i < len; i++)
			//{
			//	if((i >= this_set.size()) || (i >= other_dom_set.size()))
			//		break;
			//	met.push_back(std::make_pair(this_set[i].first & other_dom_set[i].first, 
			//				this_set[i].second & other_dom_set[i].second));
			//}

			this->dom_set.clear();
			this->dom_set = met;
		}

		ProbInvlSetDomain operator&(const ProbInvlSetDomain &other) const
		{
			if(this->is_bottom() || other.is_bottom())
				return bottom();
			else
			{
				prob_invl_set_dom_t temp = ProbInvlSetDomain(*this);
				temp.meet(other);
				return temp;
			}
		}

		void widen_with(const ProbInvlSetDomain &other)
		{
			dom_set_t widened = ProbInvlSetDomain<Number, VariableName>::dom_set_t();
			dom_set_t this_set = this->get_dom_set();
			dom_set_t other_set = other.get_dom_set();
			dom_pair_t reduced;

			std::sort(this_set.begin(), this_set.end(), ProbInvlSetDomain::doms_lt);
			std::sort(other_set.begin(), other_set.end(), ProbInvlSetDomain::doms_lt);
			std::set_union(this_set.begin(), this_set.end(),
					other_set.begin(), other_set.end(),
					std::back_inserter(widened), ProbInvlSetDomain::doms_lt);
			
			//widened = this_set | other_set;
			//this_set.insert(this_set.end(), other_set.begin(), other_set.end());
			//widened = ProbInvlSetDomain::dedup(this_set);

			if(widened.size() > JOIN_THRESHOLD)
			{
				auto widened_iter = widened.begin();
				reduced.first = widened_iter->first;
				reduced.second = widened_iter->second;
				widened_iter++;
				for(auto iter = widened_iter; iter != widened.end(); iter++)
				{
					reduced.first = reduced.first || iter->first;
					reduced.second = reduced.second || iter->second;
				}
				widened.clear();
				widened.push_back(reduced);
			}
			this->dom_set.clear();
			this->dom_set = widened;
		}

		ProbInvlSetDomain operator||(const ProbInvlSetDomain &other) const
		{
			if(this->is_bottom())
				return other;
			else if(other.is_bottom())
				return *this;
			else
			{
				ProbInvlSetDomain temp = ProbInvlSetDomain(*this);
				temp.widen_with(other);
				return temp;
			}
		}

		void narrow_with(const ProbInvlSetDomain &other)
		{
			dom_set_t other_dom_set = other.get_dom_set();
			// Should never be called
			//if(this->dom_set <= other_dom_set)
			//	this->dom_set = other_dom_set;
		}

		ProbInvlSetDomain operator&&(const ProbInvlSetDomain &other) const
		{
			if(this->is_bottom() || other.is_bottom())
				return bottom();
			else
			{
				ProbInvlSetDomain temp = ProbInvlSetDomain(*this);
				temp.narrow_with(other);
				return temp;
			}
		}

		void set(const variable_t &v, interval_t invl)
		{
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->first.set(v, invl);
			}
		}

		void set(const variable_t &v, number_t n)
		{
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->first.set(v, interval_t(n));
			}
		}

		void set(const variable_t &v, std::vector<interval_t> ivec)
		{
			int i = 0;
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				if(i >= ivec.size())
					break;
				iter->first.set(v, ivec[i]);
				i++;
			}
		}

		void set(const variable_t &v, std::vector<number_t> inum)
		{
			int i = 0;
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				if(i >= inum.size())
					break;
				iter->first.set(v, inum[i]);
				i++;
			}
		}

		interval_t at(const variable_t &v) const
		{
			interval_t invl = interval_t::bottom();
			for(auto elem : this->dom_set)
			{
				invl = invl | elem.first.at(v);
			}
			return invl;
		}

		invl_vec_t at(const var_vec_t &v) const
		{
			int i = 0;
			std::vector<interval_t> ivec = std::vector<interval_t>(this->dom_set.size(), interval_t::bottom());
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				ivec[i] = ivec[i] | iter->first.at(v[i]);
				i++;
			}
			return ivec;
		}

		void operator-=(const variable_t &v)
		{
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->first -= v;
			}
		}

		void project(const var_vec_t &vars)
		{
			if(is_bottom() || is_top()) 
			  return;
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->first.project(vars);
			}
		}

		void rename(const var_vec_t &from, const var_vec_t &to)
		{
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->first.rename(from, to);
			}
		}

		void sample(Distribution dist)
		{
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->second.sample(dist);
				//std::cerr << "Sample: " << this->dom_set[i].second.to_string() << std::endl;
			}
		}

		void reduce_rvs()
		{
			for(dom_iter_t iter = this->dom_set.begin(); iter != this->dom_set.end(); iter++)
			{
				iter->second.reduce_rvs();
			}
		}

		void write(crab::crab_os &o) const
		{
			int i = 0;
			o << "[";

			for(auto elem : this->dom_set)
			{
				o << /* "[" << elem.first << "," << */ elem.second.to_string() /*<< ")"*/;
				if(i < (this->dom_set.size() - 1))
					o << ",";
				i++;
			}
			o << "]";
		}

		std::string to_string() const
		{
			int i = 0;
			std::string res = "[";
			for(auto elem : this->dom_set)
			{
				res += elem.second.to_string();
				if(i < (this->dom_set.size() - 1))
					res += ",";
				i++;
			}
			res += "]";
			return res;
		}
			

};

} // namespace ikos
