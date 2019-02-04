package es.us.isa.ChocoReasoner.questions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerVariable;
import choco.kernel.solver.ContradictionException;
import choco.kernel.solver.Solver;
import es.us.isa.ChocoReasoner.ChocoQuestion;
import es.us.isa.ChocoReasoner.ChocoReasoner;
import es.us.isa.ChocoReasoner.ChocoResult;
import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.models.variabilityModel.VariabilityElement;
import es.us.isa.FAMA.stagedConfigManager.Configuration;

public class ChocoBOLONFMDIAG extends ChocoQuestion {

	// This should be a full configuration
	public Configuration configuration;

	// Configuration Constraints
	private Map<String, Constraint> configurationConstraints = new HashMap<String, Constraint>();
	private Map<String, Constraint> selectedConstraints = new HashMap<String, Constraint>();
	private Map<String, Constraint> deselectedConstraints = new HashMap<String, Constraint>();

	// Model Constraints
	private Map<String, Constraint> modelConstraints = new HashMap<String, Constraint>();

	// All Constraints
	private Map<String, Constraint> constraints = new HashMap<String, Constraint>();

	// All Variables
	private IntegerVariable[] variables;

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
			} else if (e.getValue() == 0) {
				configurationConstraints.put(name, Choco.eq(var, 0));
				deselectedConstraints.put(name, Choco.eq(var, 0));
			}
		}

		// Get all model constraints
		modelConstraints.putAll(((ChocoReasoner) r).getRelations());

		// Add all Constraints
		constraints.putAll(modelConstraints);
		constraints.putAll(configurationConstraints);

		// Get all model variables
		variables = ((ChocoReasoner) r).getVars();
	}

	//
	public PerformanceResult answer(Reasoner r) throws FAMAException {

		// Basic data
		ArrayList<String> S = new ArrayList<String>();
		ArrayList<String> AC = new ArrayList<String>();

		// Instantiating it for configuration extension
		AC.addAll(modelConstraints.keySet());
		AC.addAll(configurationConstraints.keySet());

		// Instantiating it for configuration extension
		S.addAll(deselectedConstraints.keySet());

		// Auxiliary data
		List<String> fmdiag = fmdiag(S, AC);

		for (String s : fmdiag) {
			result.put(s, deselectedConstraints.get(s));
		}

		return new ChocoResult();

	}

	public List<String> fmdiag(List<String> S, List<String> AC) {
		if (S.size() == 0 || !isConsistent(less(AC, S))) {
			return new ArrayList<String>();
		} else {
			return diag(new ArrayList<String>(), S, AC);
		}
	}

	public List<String> diag(List<String> D, List<String> S, List<String> AC) {
		if (D.size() != 0 && isConsistent(AC)) {
			return new ArrayList<String>();
		}

		if (S.size() == 1) {
			return S;
		}

		int k = S.size() / 2;
		List<String> S1 = S.subList(0, k);
		List<String> S2 = S.subList(k, S.size());
		List<String> A1 = diag(S2, S1, less(AC, S2));
		List<String> A2 = diag(A1, S2, less(AC, A1));
		return plus(A1, A2);
	}

	public List<String> diag2(List<String> D, List<String> S, List<String> AC) {
		if (D.size() != 0 && isConsistent(AC)) {
			return new ArrayList<String>();
		}

		if (S.size() == 1) {
			return S;
		}

		int k = S.size() / 2;
		List<String> S1 = S.subList(0, k);
		List<String> S2 = S.subList(k, S.size());
		List<String> A1 = diag(S2, S1, less(AC, S2));
		List<String> A2 = diag(new ArrayList<String>(), S2, AC);
		return plus(A1, A2);
	}

	private List<String> plus(List<String> a1, List<String> a2) {
		List<String> res = new ArrayList<String>();
		res.addAll(a1);
		res.addAll(a2);
		return res;
	}

	private List<String> less(List<String> aC, List<String> s2) {
		List<String> res = new ArrayList<String>();
		res.addAll(aC);
		res.removeAll(s2);
		return res;
	}

	private boolean isConsistent(Collection<String> aC) {
		Model p = new CPModel();
		p.addVariables(variables);

		for (String rel : aC) {
			Constraint c = constraints.get(rel);
			try {
				p.addConstraint(c);
			} catch (NullPointerException e) {
				System.err.println(rel);
			}
		}
		Solver s = new CPSolver();
		s.read(p);
		s.solve();
		return s.isFeasible();
	}
}
