/**
 * 	This file is part of FaMaTS.
 *
 *     FaMaTS is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 *
 *     FaMaTS is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU Lesser General Public License for more details.
 *
 *     You should have received a copy of the GNU Lesser General Public License
 *     along with FaMaTS.  If not, see <http://www.gnu.org/licenses/>.
 */

package es.us.isa.ChocoReasoner.questions;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import choco.Choco;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerExpressionVariable;
import choco.kernel.model.variables.integer.IntegerVariable;
import choco.kernel.solver.ContradictionException;
import choco.kernel.solver.Solver;
import choco.kernel.solver.variables.integer.IntDomainVar;
import es.us.isa.ChocoReasoner.ChocoQuestion;
import es.us.isa.ChocoReasoner.ChocoReasoner;
import es.us.isa.ChocoReasoner.ChocoResult;
import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.variabilityModel.VariabilityElement;
import es.us.isa.FAMA.stagedConfigManager.Configuration;

public class ChocoBOLON extends ChocoQuestion  {

	// This should be a full configuration
	public Configuration configuration;

	// Configuration Constraints
	private Map<String, Constraint> configurationConstraints = new HashMap<String, Constraint>();
	private Map<String, Constraint> selectedConstraints = new HashMap<String, Constraint>();
	private Map<String, IntegerVariable> deselectedVariables = new HashMap<String, IntegerVariable>();
	private Map<String, IntegerVariable> selectedVariables = new HashMap<String, IntegerVariable>();

	// Result
	public Map<String, Constraint> result = new HashMap<String, Constraint>();

	public void preAnswer(Reasoner r) {

		// Generate all configuration constraints
		for (Entry<VariabilityElement, Integer> e : configuration.getElements().entrySet()) {
			IntegerVariable var = ((ChocoReasoner) r).getVariables().get(e.getKey().getName());
			String name = "C_" + e.getKey().getName();
			if (e.getValue() > 0) {
				configurationConstraints.put(name, Choco.eq(var, 1));
				selectedConstraints.put(name, Choco.eq(var, 1));
				selectedVariables.put(name, var);
			} else if (e.getValue() == 0) {
				configurationConstraints.put(name, Choco.eq(var, 0));
				deselectedVariables.put(name, var);
			}
		}

	}

	public PerformanceResult answer(Reasoner r) throws FAMAException {
		ChocoReasoner reasoner = (ChocoReasoner) r;
		ChocoResult res = new ChocoResult();
		Solver sol = new CPSolver();
		Model p = reasoner.getProblem();
		
		//Set the hard constraints
//		for(Constraint c:selectedConstraints.values()) {
//			p.addConstraints(c);
//		}
		
		//Set the soft constraints
		IntegerVariable[] reifieds = new IntegerVariable[deselectedVariables.size()];
		IntegerVariable suma = Choco.makeIntVar("_suma", 0, deselectedVariables.size());
		IntegerExpressionVariable sumatorio = Choco.sum(deselectedVariables.values().toArray(reifieds));
		Constraint sumReifieds = Choco.eq(suma, sumatorio);
		p.addConstraint(sumReifieds);

		//Solve the problem
		sol.read(p);
		try {
			sol.propagate();
		} catch (ContradictionException e1) {
			e1.printStackTrace();
		}
		IntDomainVar maxVar = sol.getVar(suma);
		sol.minimize(maxVar, false);

		// Obtener todo los valores que tengan ese valor
		if (sol.solve() == Boolean.TRUE && sol.isFeasible()) {
				for (int i = 0; i < p.getNbIntVars(); i++) {
					IntDomainVar aux = sol.getVar(p.getIntVar(i));
					if (aux.getVal() > 0) {
						GenericFeature f = getFeature(aux, reasoner);
						if(configuration.getElements().get(f)==0) {
							String name = "C_" + f.getName();
							result.put(name,configurationConstraints.get(name));
						}
					}
				}
		}
		res.fillFields(sol);
		return res;

	}

	private GenericFeature getFeature(IntDomainVar aux, ChocoReasoner reasoner) {
		String temp = new String(aux.toString().substring(0, aux.toString().indexOf(":")));
		GenericFeature f = reasoner.searchFeatureByName(temp);
		return f;
	}



	public Class<? extends Reasoner> getReasonerClass() {
		return ChocoReasoner.class;
	}
}
