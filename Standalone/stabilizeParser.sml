let
	val _ = CM.destabilize'("parser.cm");
	val _ = CM.stabilize'("parser.cm",true); 
in  
	print("\n\n\n\nStabilize parser successful.\n\n");
	OS.Process.exit OS.Process.success 
end
