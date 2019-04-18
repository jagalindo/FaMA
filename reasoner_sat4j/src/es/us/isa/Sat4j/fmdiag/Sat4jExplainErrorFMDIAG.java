package es.us.isa.Sat4j.fmdiag;

import static es.us.isa.Sat4j.fmdiag.DiagHelpers.less;
import static es.us.isa.Sat4j.fmdiag.DiagHelpers.plus;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.Reasoner.questions.ExplainErrorsQuestion;
import es.us.isa.FAMA.errors.Error;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.Sat4jReasoner.Sat4jQuestion;
import es.us.isa.Sat4jReasoner.Sat4jReasoner;
import es.us.isa.Sat4jReasoner.Sat4jResult;

public class Sat4jExplainErrorFMDIAG extends Sat4jQuestion implements ExplainErrorsQuestion {

	public boolean returnAllPossibeExplanations = false;
	private Sat4jReasoner reasoner;
	public Map<String, String> result = new HashMap<String, String>();
	String cnf_content = "c CNF file\n";
	String clauses = "";
	Map<String, String> relations = null;
	public boolean flexactive = false;
	public int m = 1;

	Product s, r;

	public void setConfiguration(Product s) {
		this.s = s;
	}

	public void setRequirement(Product r) {
		this.r = r;
	}

	public PerformanceResult answer(Reasoner r) throws FAMAException {
		reasoner = (Sat4jReasoner) r;
		// solve the problem y fmdiag
		relations = new HashMap<String, String>();

		Map<String, String> productConstraint = new HashMap<String, String>();
		ArrayList<String> feats = new ArrayList<String>();
		for (GenericFeature f : this.s.getFeatures()) {
			String cnfVar = reasoner.getCNFVar(f.getName());
			String name = "U_" + f.getName();
			productConstraint.put(name, "-" + cnfVar + " 0");
			feats.add(name);
		}

		Map<String, String> requirementConstraint = new HashMap<String, String>();
		for (GenericFeature f : this.r.getFeatures()) {
			String cnfVar = reasoner.getCNFVar(f.getName());
			requirementConstraint.put("R_" + f.getName(), cnfVar + " 0");
		}

		int cindex = 0;
		for (String cl : reasoner.clauses) {
			relations.put(cindex + "rel", cl);
		}
		relations.putAll(requirementConstraint);
		relations.putAll(productConstraint);

		Iterator<String> it = reasoner.variables.keySet().iterator();
		while (it.hasNext()) {
			String varName = it.next();
			cnf_content += "c var " + reasoner.variables.get(varName) + " = " + varName + "\n";
		}

		for (String cons : reasoner.clauses) {
			clauses += (String) cons + "\n";

		}

		List<String> S = new ArrayList<String>(feats);
		List<String> AC = new ArrayList<String>(relations.keySet());

		if (returnAllPossibeExplanations == false) {
			List<String> fmdiag = fmdiag(S, AC);
			for (String s : fmdiag) {
				result.put(s, productConstraint.get(s));
			}
		} else {
			List<String> allExpl = new LinkedList<String>();
			List<String> fmdiag = fmdiag(S, AC);
			while (fmdiag.size() != 0) {
				allExpl.addAll(fmdiag);
				S.removeAll(fmdiag);
				AC.removeAll(fmdiag);
				fmdiag = fmdiag(S, AC);
			}
			for (String s : allExpl) {
				result.put(s, productConstraint.get(s));
			}

		}
		return new Sat4jResult();

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



	private boolean isConsistent(Collection<String> aC) {

		// Start the problem
		String cnf_content = new String(this.cnf_content);
		cnf_content += "p cnf " + reasoner.variables.size() + " " + (aC.size()+reasoner.clauses.size()) + "\n";

		// Configuration clauses
		for (String cons : aC) {
			cnf_content += (String) relations.get(cons) + "\n";

		}

		cnf_content+=clauses;

		// End file
		cnf_content += "0";
		ByteArrayInputStream stream = new ByteArrayInputStream(cnf_content.getBytes(StandardCharsets.UTF_8));

		ISolver s = SolverFactory.newDefault();
		Reader reader = new DimacsReader(s);
		try {
			reader.parseInstance(stream);
			return s.isSatisfiable();
		} catch (TimeoutException | ParseFormatException | ContradictionException | IOException e) {
			// e.printStackTrace();

		}
		return false;

	}

	@Override
	public void setErrors(Collection<Error> colErrors) {
		System.err.println("Do not use this method");
	}

	@Override
	public Collection<Error> getErrors() {
		System.err.println("Do not use this method");
		return null;
	}

}
