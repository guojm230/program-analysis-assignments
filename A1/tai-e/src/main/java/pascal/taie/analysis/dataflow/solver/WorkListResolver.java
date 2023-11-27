package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;

public class WorkListResolver<Node,Fact> extends Solver<Node,Fact>{

    protected WorkListResolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        var workList = new LinkedList<>(cfg.getNodes());
        while (!workList.isEmpty()){
            var node = workList.pop();
            var outFact = analysis.newInitialFact();
            var inFact = result.getInFact(node);

            for (Node succNode : cfg.getSuccsOf(node)) {
                analysis.meetInto(result.getInFact(succNode),outFact);
            }

            result.setOutFact(node,outFact);

            if (analysis.transferNode(node,inFact,outFact)){
                workList.addAll(cfg.getPredsOf(node));
            }
        }
    }
}
