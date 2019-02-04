package es.us.isa.Choco.fmdiag.configuration;

import static choco.Choco.eq;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.Callable;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;

import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerExpressionVariable;
import choco.kernel.model.variables.integer.IntegerVariable;
import choco.kernel.solver.Solver;
import es.us.isa.ChocoReasoner.ChocoQuestion;
import es.us.isa.ChocoReasoner.ChocoReasoner;
import es.us.isa.ChocoReasoner.ChocoResult;
import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.Reasoner.questions.ExplainErrorsQuestion;
import es.us.isa.FAMA.errors.Error;
import es.us.isa.FAMA.errors.Observation;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.variabilityModel.VariabilityElement;

public class ChocoExplainErrorFMDIAGParalell extends ChocoQuestion implements ExplainErrorsQuestion {

	public boolean returnAllPossibeExplanations = false;
	private ChocoReasoner chReasoner;
	public List<String> explanations;

	Collection<Error> errors;
	Map<String, Constraint> relations = null;
	//int numberOfThreads = Runtime.getRuntime().availableProcessors();

  int numberOfThreads = 1;
	
	ExecutorService executorService = Executors.newCachedThreadPool();


	public PerformanceResult answer(Reasoner r) throws FAMAException {

		ChocoResult res = new ChocoResult();
		chReasoner = (ChocoReasoner) r;

		if ((errors == null) || errors.isEmpty()) {
			errors = new LinkedList<Error>();
			return res;
		}

		Iterator<Error> itE = this.errors.iterator();
		Map<String, IntegerVariable> vars = chReasoner.getVariables();
		Map<String, IntegerExpressionVariable> setVars = chReasoner.getSetRelations();
		// mientras haya errores
		while (itE.hasNext()) {
			// crear una lista de constraints, que impondremos segun las
			// observaciones
			Error e = itE.next();

			// System.out.println("Explanations for "+e.toString());
			Map<String, Constraint> cons4obs = new HashMap<String, Constraint>();
			Observation obs = e.getObservation();
			Map<? extends VariabilityElement, Object> values = obs.getObservation();
			Iterator<?> its = values.entrySet().iterator();

			// mientras haya observations
			// las imponemos al problema como restricciones
			while (its.hasNext()) {
				int i = 0;
				try {
					Entry<? extends VariabilityElement, Object> entry = (Entry<? extends VariabilityElement, Object>) its
							.next();
					Constraint cn;
					int value = (Integer) entry.getValue();
					VariabilityElement ve = entry.getKey();
					if (ve instanceof GenericFeature) {
						IntegerVariable arg0 = vars.get(ve.getName());
						cn = eq(arg0, value);
					} else {
						IntegerExpressionVariable arg0 = setVars.get(ve.getName());
						cn = eq(arg0, value);
					}
					cons4obs.put("Temporary" + i, cn);
					i++;
				} catch (ClassCastException exc) {
				}
			}

			// solve the problem y fmdiag
			relations = new HashMap<String, Constraint>();
			relations.putAll(cons4obs);
			relations.putAll(chReasoner.getRelations());

			CopyOnWriteArrayList<String> S = new CopyOnWriteArrayList<String>(chReasoner.getRelations().keySet());	
	//		ArrayList<String> S = new ArrayList<String>(chReasoner.getRelations().keySet());
			CopyOnWriteArrayList<String> AC = new CopyOnWriteArrayList<String>(relations.keySet());
	//		ArrayList<String> AC = new ArrayList<String>(relations.keySet());

			if (returnAllPossibeExplanations == false) {
				List<String> fmdiag = fmdiag(S, AC);
				// System.out.println("Relation "+fmdiag.get(0)+" is causing the
				// conflict");
				explanations = fmdiag;
			} else {
				List<String> allExpl = new LinkedList<String>();
				List<String> fmdiag = fmdiag(S, AC);
				while (fmdiag.size() != 0) {
					allExpl.addAll(fmdiag);
					S.removeAll(fmdiag);
					AC.removeAll(fmdiag);
					fmdiag = fmdiag(S, AC);
				}
				explanations = fmdiag;
				// for(String str:allExpl){
				// System.out.println("Relation "+str+" is causing the
				// conflict");
				// }
			}

		}
		return new ChocoResult();

	}

	public CopyOnWriteArrayList<String> fmdiag(CopyOnWriteArrayList<String> S, CopyOnWriteArrayList<String> AC) {
		//S is empty or (AC - S) non-consistent
		if (S.size() == 0 || !isConsistent(less(AC, S))) {
			return new CopyOnWriteArrayList<String>();
		} 
		else { 		
			//(AC + S) is non-consistent
			ForkJoinPool pool = new ForkJoinPool(numberOfThreads);
			diagThreadsFJ dt = new diagThreadsFJ(new CopyOnWriteArrayList<String>(), S, AC, numberOfThreads);
			CopyOnWriteArrayList<String> solution = pool.invoke(dt);
			return solution;
		}
	}

	public class diagThreadsFJ extends RecursiveTask<CopyOnWriteArrayList<String>>{
		CopyOnWriteArrayList<String> D, S, AC;
		int numberOfSplits;
		ExecutorService executorService;

		CPModel p = new CPModel();
		
	    
		public diagThreadsFJ(CopyOnWriteArrayList<String> D, CopyOnWriteArrayList<String> S,CopyOnWriteArrayList<String> AC, int numberOfSplits){
			this.D=D;
			this.S=S;
			this.AC=AC;
//			this.executorService=executorService;
			this.numberOfSplits=numberOfSplits;	
		
			p.addVariables(chReasoner.getVars());
		 }
		
		/*Each thread (instance of this class) presents values for its attributes D, S, and AC. 
		 *(D + S) represents the set of rules to analyze; D and S are complementary, and S 
		 *corresponds to the current solution set.
		 *
		 *At the start point of the call() method , always:
		 *	- S represents the solution set.
		 *	- D represents the complement set of S concerning the previous solution set.
		 *	- AC represents the consistent rules of model C + the rules of S.  
		 *
		 *For the 1st thread always D is empty and S inconsistent. Then, AC is inconsistent.*/
		
		public CopyOnWriteArrayList<String> compute(){		
        long threadId = Thread.currentThread().getId();
        int paso=1;
        
		/*1st base case*/		
		if (D.size() != 0 && isConsistent(AC, this)){	
		   /*Since AC does not contain D, when D is not empty and AC is consistent, 
		    *then D contains inconsistencies then D is analyzed to look for them*/
	  	    return new CopyOnWriteArrayList<String>();				
		}
		
		/*Since AC is non-consistent and D is not the inconsistencies source, then S is their source.
		 *If this algorithmic solution is 'flexible' and the size of S is lesser or equal than m, then 
		 *S is the looked inconsistencies set (m defines the solution flexibility to 
		 *contains some consistent rules). 
		 *
		 *If this solution is not 'flexible' and S contains only one rule, then S is the looked inconsistent set*/
		
		/*2nd base case*/
		if (S.size()==1){
	    	   return S;
		}
		
		
		/*outList corresponds to a results list for the threads of the solution*/
		CopyOnWriteArrayList<CopyOnWriteArrayList<String>> outLists= 
				new CopyOnWriteArrayList<CopyOnWriteArrayList<String>>();
	
		////*DIVISION PHASE*////
		int div = 0; //div is the size of the partitions
					
		if (S.size() >= numberOfSplits){
		   div = S.size() / numberOfSplits;
		   if ((S.size() % numberOfSplits)>0)
			   div++;
		}
		else 
			div = 1;
		
		CopyOnWriteArrayList<CopyOnWriteArrayList<String>> splitListToSubLists = 
				splitListToSubLists(S, div);
		int actDiv = 0, maxDiv = splitListToSubLists.size();
		
		CopyOnWriteArrayList<RecursiveTask<CopyOnWriteArrayList<String>>> forks = new CopyOnWriteArrayList<>();
		
		////*CONQUER PHASE*////
		int i = 1;
		for(CopyOnWriteArrayList<String> s: splitListToSubLists){
			/*For each partition 's', we define its complement 'rest' (AC - s) and  
			 *the rules set 'less' (AC - rest). 
			 *Then, a new thread 'dt' is defined with D=rest, S=s, and AC=less, 'dt' is run,
			 *and its results are grouped in the results list*/ 		
			if (actDiv == (maxDiv-1))
				break;

			CopyOnWriteArrayList<String> rest= getRest(s,splitListToSubLists);	
			CopyOnWriteArrayList<String> less = less(AC,rest);

			diagThreadsFJ dt = new diagThreadsFJ(rest, s, less , numberOfSplits);
			dt.fork();
			
			forks.add(dt);
			
			if (actDiv < (maxDiv-1))
				actDiv++;
							
			i++;
		}

		/*
		int r=0, rr=-1;
		for(RecursiveTask<CopyOnWriteArrayList<String>> subTask: forks){
	       outLists.add(subTask.join());
	       
	       if (outLists.get(outLists.size()-1).isEmpty() && rr==-1)
	    	   rr=r;
	       
	       r++;
		}
		*/

		/*We save and return the union of the results of lists*/
		CopyOnWriteArrayList<String> fullSolution1 = plus(outLists);

		/*FMDiag 2nd call*/
		CopyOnWriteArrayList<String> s = splitListToSubLists.get(actDiv);
		CopyOnWriteArrayList<String> less = less(AC,fullSolution1);
		
		diagThreadsFJ dt = new diagThreadsFJ(fullSolution1, s, less, numberOfSplits);
		dt.fork();
		
		outLists.add(dt.join());						
		CopyOnWriteArrayList<String> fullSolution = plus(outLists);
		
		return fullSolution;
	}
		
		private CopyOnWriteArrayList<String> getRest(CopyOnWriteArrayList<String> s2, CopyOnWriteArrayList<CopyOnWriteArrayList<String>> splitListToSubLists) {
			CopyOnWriteArrayList<String> res= new CopyOnWriteArrayList<String>();

			for(CopyOnWriteArrayList<String> c: splitListToSubLists){
				if(c!=s2){
					res.addAll(c);
				}
			}
			return res;
		}

		private CopyOnWriteArrayList<String> plus(CopyOnWriteArrayList<CopyOnWriteArrayList<String>> outLists) {
			CopyOnWriteArrayList<String> res=new CopyOnWriteArrayList<String>();
			for(List<String> s:outLists){	
				res.addAll(s);
			}
			return res;
		}

		public <T> CopyOnWriteArrayList<CopyOnWriteArrayList<T>> splitListToSubLists(
				CopyOnWriteArrayList<T> parentList, int subListSize) {
			
		  CopyOnWriteArrayList<CopyOnWriteArrayList<T>> subLists = new CopyOnWriteArrayList<CopyOnWriteArrayList<T>>();
		  
		  if (subListSize > parentList.size()) {
		     subLists.add(parentList);
		     } 
		  else {
		     int remainingElements = parentList.size();
		     int startIndex = 0;
		     int endIndex = subListSize;
		     do {
		    	 List<T> subList =  parentList.subList(startIndex, endIndex);
		         subLists.add(new CopyOnWriteArrayList<T>(subList));
		         startIndex = endIndex;
		        if (remainingElements - subListSize >= subListSize) {
		           endIndex = startIndex + subListSize;
		        } else {
		           endIndex = startIndex + remainingElements - subList.size();
		        }
		        remainingElements -= subList.size();
		     } while (remainingElements > 0);

		  }
		  return subLists;	
		}
   }

	public <T> List<List<T>> splitListToSubLists(List<T> parentList, int subListSize) {
		List<List<T>> subLists = new ArrayList<List<T>>();
		  
		if (subListSize > parentList.size()) {
		   subLists.add(parentList);
		 } 
		else {
		   int remainingElements = parentList.size();
		   int startIndex = 0;
		   int endIndex = subListSize;
		   do {
		      List<T> subList = parentList.subList(startIndex, endIndex);
		      subLists.add(subList);
		      startIndex = endIndex;
		      if (remainingElements - subListSize >= subListSize) {
		         endIndex = startIndex + subListSize;
		      } else {
		         endIndex = startIndex + remainingElements - subList.size();
		      }
		      remainingElements -= subList.size();
		   } while (remainingElements > 0);

		}
		return subLists;
	}
	
	private CopyOnWriteArrayList<String> less(CopyOnWriteArrayList<String> aC, CopyOnWriteArrayList<String> s2) {
		CopyOnWriteArrayList<String> res = new CopyOnWriteArrayList<String>();
		res.addAll(aC);
		res.removeAll(s2);
		return res;
	}
	
	private boolean isConsistent(Collection<String> aC) {
   		CPModel p = new CPModel();
		p.addVariables(chReasoner.getVars()); 
				   			   
		for (String rel : aC) {
		    Constraint c = relations.get(rel);

		    if (c == null) {
			    System.out.println("Error");
			 }
	        p.addConstraint(c);
		   }

		Solver s = new CPSolver();
		s.read(p);
		s.solve();

		return s.isFeasible();
	}

	private boolean isConsistent(Collection<String> aC, diagThreadsFJ currentThread) {			
	   CPModel p = currentThread.p;
		   
	   for (String rel : aC) {
		   Constraint c = relations.get(rel);

	  	   if (c == null) {
			   System.out.println("Error");
		   }
		   p.addConstraint(c);
	   }

	   Solver s = new CPSolver();
	   s.read(p);
	   s.solve();

	   return s.isFeasible();
	}

	public void setErrors(Collection<Error> colErrors) {
		this.errors= colErrors;
	}

	public Collection<Error> getErrors() {
		return errors;
	}
}