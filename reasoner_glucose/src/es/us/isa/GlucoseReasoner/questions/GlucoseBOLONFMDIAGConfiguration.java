package es.us.isa.GlucoseReasoner.questions;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.models.variabilityModel.VariabilityElement;
import es.us.isa.FAMA.stagedConfigManager.Configuration;
import es.us.isa.GlucoseReasoner.GlucoseQuestion;
import es.us.isa.GlucoseReasoner.GlucoseReasoner;
import es.us.isa.GlucoseReasoner.GlucoseResult;

public class GlucoseBOLONFMDIAGConfiguration extends GlucoseQuestion {

	// This should be a full configuration
	public Configuration configuration;

	// Configuration Constraints
	/*
	 * private Map<String, Boolean> configurationConstraints = new HashMap<String,
	 * Boolean>(); private Map<String, Boolean> selectedConstraints = new
	 * HashMap<String, Boolean>(); private Map<String, Boolean>
	 * deselectedConstraints = new HashMap<String, Boolean>();
	 * 
	 * // Model Constraints private Map<String, Boolean> modelConstraints = new
	 * HashMap<String, Boolean>();
	 */
	private ArrayList<String> configurationConstraints = new ArrayList<String>();
	private ArrayList<String> selectedConstraints = new ArrayList<String>();
	private ArrayList<String> deselectedConstraints = new ArrayList<String>();

	// Model Constraints
	private ArrayList<String> modelConstraints = new ArrayList<String>();

	// All Constraints
	private ArrayList<String> constraints = new ArrayList<String>();

	// All Variables
	private Map<String, String> variables;

	// Result
	public ArrayList<String> result = new ArrayList<String>();

	private GlucoseReasoner reasoner;

	public void preAnswer(Reasoner r) {
		reasoner = (GlucoseReasoner) r;

		// Generate all configuration constraints
		for (Entry<VariabilityElement, Integer> e : configuration.getElements().entrySet()) {
			String var = ((GlucoseReasoner) r).getVariables().get(e.getKey().getName());
			String name = "C_" + e.getKey().getName();

			configurationConstraints.add(name);

			if (e.getValue() > 0) {
				selectedConstraints.add(name);
			} else if (e.getValue() == 0) {
				deselectedConstraints.add(name);
			}
		}

		// Get all model constraints
		modelConstraints = ((GlucoseReasoner) r).getClauses();

		// Add all Constraints
		constraints.addAll(modelConstraints);
		constraints.addAll(configurationConstraints);

		// Get all model variables
		variables = ((GlucoseReasoner) r).variables;

	}

	//
	public PerformanceResult answer(Reasoner r) throws FAMAException {

		// Basic data
		ArrayList<String> S = new ArrayList<String>();
		ArrayList<String> AC = new ArrayList<String>();

		// Instantiating it for configuration extension
		AC.addAll(modelConstraints);
		AC.addAll(configurationConstraints);

		// Instantiating it for configuration extension
		S.addAll(deselectedConstraints);

		// Auxiliary data
		List<String> fmdiag = fmdiag(S, AC);

		for (String s : fmdiag) {
			result.add(s);
		}

		return new GlucoseResult();

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

	/*
	 * private boolean isConsistent(Collection<String> aC) { Model p = new
	 * CPModel(); //p.addVariables(variables);
	 * 
	 * for (String rel : aC) { Constraint c = constraints.get(rel); try {
	 * p.addConstraint(c); }catch (NullPointerException e) {
	 * System.err.println(rel); } } Solver s = new CPSolver(); s.read(p); s.solve();
	 * return s.isFeasible(); }
	 */

	private boolean isConsistent(Collection<String> aC) {
		// First we create the content of the cnf
		String cnf_content = "c CNF file\n";

		// We show as comments the variables's number
		Iterator<String> it = reasoner.variables.keySet().iterator();
		while (it.hasNext()) {
			String varName = it.next();
			cnf_content += "c var " + reasoner.variables.get(varName) + " = " + varName + "\n";
		}

		// Start the problem
		cnf_content += "p cnf " + reasoner.variables.size() + " " + (-1 + modelConstraints.size()) + "\n";
		// Clauses
		it = modelConstraints.iterator();
		while (it.hasNext()) {
			cnf_content += (String) it.next() + "\n";
		}

		// End file
		cnf_content += "0";
		boolean res = false;
		try {
			//File tmpFile = File.createTempFile("cnf", "fm");
			File tmpFile = new File("C:\\glucose\\test.cnf");
			PrintWriter out = new PrintWriter(tmpFile);
			out.print(cnf_content);
			out.close();
			Process p = Runtime.getRuntime().exec("bash.exe -c \"/mnt/c/glucose/glucose /mnt/c/glucose/test.cnf\"");
			BufferedReader stdInput = new BufferedReader(new 
				     InputStreamReader(p.getInputStream()));
			String outStr ="";
			String s = null;
			while ((s = stdInput.readLine()) != null) {
			    outStr+=s;
			}
			res=outStr.contains("UNSATISFIABLE");
			
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return res;

	}
	
}
