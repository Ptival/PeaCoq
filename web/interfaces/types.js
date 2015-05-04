/* @flow */

type Group = {
	name: string;
	tactics: Array < string > ;
};

type Hypothesis = {
	hName: string;
	hValue: {
		contents: string;
		tag: string;
	};
	hType: {
		contents: string;
		tag: string;
	};
};
