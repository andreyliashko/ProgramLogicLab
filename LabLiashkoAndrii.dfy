//input test data
class TestData{
    var sequence:seq<real>
     var start_time:Time
     var finish_time:Time
     
    constructor(){
        sequence := [16200.12, 16201.08, 16203.96, 16211.6, 16212.52, 16213.44, 16214.36, 16215.32, 16216.24, 16220.84,
                16222.8, 16223.32, 16224.52, 16229.88, 16230.44, 16231.12, 16231.72, 16232.92, 16233.44, 16234.04,
                16236.36, 16237.28, 16238.2, 16239.64, 16240.24, 16240.8, 16241.64, 16242.16, 16243.28, 16244.2,
                16246.8, 16251.64, 16252.32, 16252.92, 16254.68, 16258.32, 16259.28, 16264.48, 16265.92, 16267.08,
                16270.64, 16271.16, 16272.32, 16273.52, 16274.76, 16275.32, 16278.24, 16279.16, 16282.72, 16283.64,
                16284.16, 16286.56, 16288.92, 16290.64, 16292.6, 16294.2, 16295.48, 16296.48, 16299.12, 16301.76,
                16303.0, 16303.52, 16307.12, 16308.08, 16308.6, 16309.92, 16313.28, 16315.56, 16316.72, 16317.84,
                16321.76, 16325.28, 16325.84, 16327.16, 16328.24, 16328.8, 16329.36, 16331.8, 16332.36, 16332.92,
                16335.36, 16339.88, 16340.92, 16344.44, 16345.6, 16348.4, 16349.32, 16351.12, 16352.04, 16354.8,
                16356.72, 16357.68, 16358.64, 16359.6, 16362.4, 16369.08, 16370.04, 16371.0, 16371.96, 16372.92];
        start_time := new Time(4.0, 30.0, 0.0, 0.0);
        finish_time := new Time(5.0, 0.0, 0.0, 0.0);
        
    }
}

//class Time
class Time {
    var hours: real
    var minutes: real
    var seconds: real
    var milis: real
    

    constructor(hour: real, minute: real, sec: real, mil: real)
        ensures hours == hour && minutes == minute && seconds == sec && milis == mil
    {
        hours := hour;
        minutes := minute;
        seconds := sec;
        milis := mil;
        
    }
}
//class for delete unused intervals
class AutoDelGr{
    constructor(){}
}
//start varialbles of program
class InputVariables{
    var delta_time: real
    var points_per_sec: int
    constructor(){
        var delta_time := 0.01;
        var points_per_sec := 5;
    }
    method get_delta_time() returns (delta_time:real){
        return this.delta_time;
    }
    method get_points_per_sec() returns (points_per_sec:int){
        return this.points_per_sec;
    }
}
// main method? what used to analyze input array and return needed intervals
class DeleteByQRS {
    var peak_x: seq<real>
    var start: Time
    var finish: Time 
    var autoDel:AutoDelGr
    var inputVariables: InputVariables
   
    //peaks of EKG 
    constructor(peak_x: seq<real>, start: Time, finish: Time, autoDel: AutoDelGr) {
        this.peak_x := peak_x;
        this.start := start;
        this.finish := finish;
        this.autoDel := autoDel;
        inputVariables := new InputVariables();
    }

    // method only to find points at this time period
    method find_nearest_data() returns (result:real){
        result := 0.0;
        return result;
    }

   // main method
    method FindChains(sequence: seq<real>) returns (chains: seq<real>)
    requires forall j, k :: 0 <= j < k < |sequence| ==> sequence[k] <= sequence[j] //conditions before work
    requires |sequence|>=1 
    ensures |sequence|>=1 //post condition after work
    ensures |chains|>=0

    
    {
        
        var delta_time_seconds:real := 0.001;
        var delta_points:int := 5;
        
        chains := [];
        var currentChain: seq<real> := [];
        var i:int := 0;

        while i < |sequence|-1
            invariant 0 <= i <= |sequence| //show the correctness of cycle
            decreases |sequence| - i

        {
            if sequence[i+1]-sequence[i] < delta_time_seconds{
                if |currentChain| == 0{
                    currentChain := currentChain + [sequence[i]];
                }
                currentChain := currentChain +[sequence[i+1]];
            }
            else{
                if |currentChain|>delta_points{
                    chains := chains +currentChain;
                }
                currentChain := [];
            }
            if |currentChain| > delta_points{
                chains := chains + [currentChain[0], currentChain[|currentChain| - 1]];
            }
            i := i + 1;
        }
        
        return chains;

    }

        
}

method main() {
    
    var autoDelGr := new AutoDelGr();
    var testData :TestData := new TestData();
    var dbqrs := new DeleteByQRS(testData.sequence, testData.start_time, testData.finish_time, autoDelGr);
    var sequences := dbqrs.FindChains(testData.sequence);
}
