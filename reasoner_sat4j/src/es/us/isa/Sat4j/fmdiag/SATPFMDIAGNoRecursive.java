package es.us.isa.Sat4j.fmdiag;

import static es.us.isa.Sat4j.fmdiag.DiagHelpers.getRest;
import static es.us.isa.Sat4j.fmdiag.DiagHelpers.less;
import static es.us.isa.Sat4j.fmdiag.DiagHelpers.plus;
import static es.us.isa.Sat4j.fmdiag.DiagHelpers.splitListToSubLists;

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
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;
import java.util.concurrent.RecursiveTask;

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
import es.us.isa.FAMA.Reasoner.questions.ValidConfigurationErrorsQuestion;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.Sat4jReasoner.Sat4jQuestion;
import es.us.isa.Sat4jReasoner.Sat4jReasoner;
import es.us.isa.Sat4jReasoner.Sat4jResult;

public class SATPFMDIAGNoRecursive extends Sat4jQuestion implements ValidConfigurationErrorsQuestion {

	public boolean returnAllPossibeExplanations = false;
	public int numberOfThreads;
	String cnf_content = "c CNF file\n";		String clauses="";

	ForkJoinPool pool = null;

	private Sat4jReasoner reasoner;

	Map<String, String> relations = null;

	Product s, r;
	public Map<String, String> result = new HashMap<String, String>();

	public void setConfiguration(Product s) {
		this.s = s;
	}

	public void setRequirement(Product r) {
		this.r = r;
	}

	public SATPFMDIAGNoRecursive(int t) {
		this.numberOfThreads = t;
		this.pool = new ForkJoinPool(numberOfThreads);
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


		// First we create the content of the cnf file that's to be used by the consistent function
		// We show as comments the variables's number
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
			List<String> fmdiag = pfmdiag(S, AC);
			for (String s : fmdiag) {
				result.put(s, productConstraint.get(s));
			}

		} else {
			List<String> allExpl = new LinkedList<String>();
			List<String> fmdiag = pfmdiag(S, AC);

			while (fmdiag.size() != 0) {
				allExpl.addAll(fmdiag);
				S.removeAll(fmdiag);
				AC.removeAll(fmdiag);
				fmdiag = pfmdiag(S, AC);
			}
			for (String s : allExpl) {
				result.put(s, productConstraint.get(s));
			}
		}

		return new Sat4jResult();
	}

	public List<List<String>> divideSet(int numberOfSplits, List<String> S) {
		int div = 0; // div is the size of the partitions

		if (S.size() >= numberOfSplits) {
			div = S.size() / numberOfSplits;
			if ((S.size() % numberOfSplits) > 0)
				div++;
		} else
			div = 1;

		return splitListToSubLists(S, div);
	}

	public List<String> pfmdiag(List<String> S, List<String> AC) {
		if (S.size() == 0 || !isConsistent(less(AC, S))) {
			return new LinkedList<String>();
		} else {
			// Divido S en n partes

			Collection<ForkJoinTask<List<String>>> futures = new LinkedList<ForkJoinTask<List<String>>>();

			List<String> solution = new LinkedList<String>();

			List<List<String>> S_SET = divideSet(numberOfThreads, S);
			for (List<String> S_i : S_SET) {

				// Calculo los restos de cada parte
				List<String> rest = getRest(S_i, S_SET);
				List<String> less = less(AC, rest);

				// Genero un thread por cada uno y ejecuto

				Diagthread dt = new Diagthread(rest, S, less);
				pool.execute(dt);

				futures.add(dt);
//				System.out.println(Thread.activeCount());
			}
			// System.out.println(Thread.activeCount());
			// pool.invokeAll(futures);
			for (ForkJoinTask<List<String>> subTask : futures) {
				solution.addAll(subTask.join());
			}

			/* We save and return the union of the results of lists */
			// List<String> fullSolution1 = plus(outLists);

			/* FMDiag 2nd call */
			// List<String> s = splitListToSubLists.get(actDiv);
			List<String> less = less(AC, solution);

			Diagthread dt = new Diagthread(solution, S, less);
			// dt.fork();

			return dt.invoke();
		}
	}

	public class Diagthread extends RecursiveTask<List<String>> {

		private static final long serialVersionUID = -7886822924012231609L;

		List<String> D, S, AC;

		public Diagthread(List<String> D, List<String> S, List<String> AC) {
			this.D = D;
			this.S = S;
			this.AC = AC;

		}

		public List<String> compute() {
			return diag(this.D, this.S, this.AC);
		}

		public List<String> diag(List<String> D, List<String> S, List<String> AC) {
			if (D.size() != 0 && isConsistent(AC)) {
				return new ArrayList<String>();
			}

			if (S.size() == 1) {
				return S;
			}

			int k = S.size() / 2;
			List<String> S1 = new ArrayList<String>(S.subList(0, k));
			List<String> S2 = new ArrayList<String>(S.subList(k, S.size()));

			List<String> A1 = diag(S2, S1, less(AC, S2));
			List<String> A2 = diag(A1, S2, less(AC, A1));
			return plus(A1, A2);
		}

	}

	private boolean isConsistent(Collection<String> aC) {

		// Start the problem
		String cnf_content=new String(this.cnf_content);
		cnf_content += "p cnf " + reasoner.variables.size() + " " + (aC.size()+reasoner.clauses.size()) + "\n";
	
//		cnf_content+=clauses;
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
			//e.printStackTrace();

		}
		return false;

	}

	@Override
	public void setProduct(Product p) {
		System.err.println("Do not use this method");
	}

	@Override
	public boolean isValid() {
		System.err.println("Do not use this method");
		return false;
	}

}