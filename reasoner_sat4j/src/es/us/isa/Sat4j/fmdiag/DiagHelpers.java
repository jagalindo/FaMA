package es.us.isa.Sat4j.fmdiag;

import java.util.LinkedList;
import java.util.List;

public class DiagHelpers {

	
	@SafeVarargs
	public static List<String> plus(List<String> ... lists) {
		List<String> res = new LinkedList<String>();
		for (List<String> s : lists) {
			res.addAll(s);
		}
		return res;
	}

	public static List<String> plus(List<List<String>> outLists) {
		List<String> res = new LinkedList<String>();
		for (List<String> s : outLists) {
			res.addAll(s);
		}
		return res;
	}
	
	public static List<String> less(List<String> minuendo, List<String> sustraendo) {
		List<String> res = new LinkedList<String>();
		res.addAll(minuendo);
		res.removeAll(sustraendo);
		return res;
	}

	public static List<String> getRest(List<String> selected, List<List<String>> allList) {
		List<String> res = new LinkedList<String>();

		for (List<String> currentList : allList) {
			if (currentList != selected) {
				res.addAll(currentList);
			}
		}
		
		return res;
	}

	public static <T> List<List<T>> splitListToSubLists(List<T> parentList, int subListSize) {

		List<List<T>> subLists = new LinkedList<List<T>>();

		if (subListSize > parentList.size()) {
			subLists.add(parentList);
		} else {
			int remainingElements = parentList.size();
			int startIndex = 0;
			int endIndex = subListSize;
			do {
				List<T> subList = parentList.subList(startIndex, endIndex);
				subLists.add(new LinkedList<T>(subList));
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
