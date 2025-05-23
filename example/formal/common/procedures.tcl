proc my_parray {a {pattern *}} {
    upvar 1 $a array
    if {![array exists array]} {
        return -code error "\"$a\" isn't an array"
    }
    set maxl 0
    set names [lsort [array names array $pattern]]
    foreach name $names {
        if {[string length $name] > $maxl} {
            set maxl [string length $name]
        }
    }
    set maxl [expr {$maxl + [string length $a] + 2}]
    set ret_str ""
    foreach name $names {
        set nameString [format %s(%s) $a $name]
        set ret_str "$ret_str\n[format "%-*s = %s" $maxl $nameString $array($name)]"
    }
    return $ret_str
}

proc flow_log {severity message} {
  set log_label {-error}
  set tag ""
  set echo 1
  set invocation_level [info frame]
  set invocation_level [expr $invocation_level - 1]
  set dbg_info [info frame $invocation_level]
  set file [info script]
  set line [dict get $dbg_info line]
  #upvar 0 $flow_log_verbosity flv
  if {![info exists flow_log_verbosity]} {
    set flow_log_verbosity 1
  }
  if {[string equal -nocase $severity error]} {
    # Error has verbosity 0 and above
    set log_label {-error -file $file -line $line}
    set echo [expr $flow_log_verbosity >= 0]
  } elseif {[string equal -nocase $severity info]} {
    # Info has verbosity 1 and above
    set log_label {-info}
    set echo [expr $flow_log_verbosity >= 1]
  } elseif {[string equal -nocase $severity warn]} {
    # Warn has verbosity 1 and above
    set log_label {-warning -file $file -line $line}
    set echo [expr $flow_log_verbosity >= 1]
  } elseif {[string equal -nocase $severity debug]} {
    # Debug has verbosity 2 and above
    set log_label {-info -file $file -line $line}
    set tag "DEBUG"
    set echo [expr $flow_log_verbosity >= 2]
  } else {
    put_message "Invalid logger label!" $log_label
  }
  if {$echo} {
    if {[string length $tag]} {
      put_message $message $log_label -tag $tag
    } else {
      put_message $message $log_label
    }
  }
}

proc generate_toggle_assumes_for_superlint {{signals_to_exclude ""}} {
  ### This procedure is to be called only after analyze, elaborate, clock and reset steps!

  # Get all input signals
  set all_inputs [get_design_info -list input -silent]
  # Get all clocks
  set all_clocks [clock -list signal -silent]
  # Get all resets
  set all_resets [reset -list signal -silent]
  set inputs_no_clk_no_reset $all_inputs
  # Remove each clock from inputs list
  foreach clk $all_clocks {
    set inputs_no_clk_no_reset [lsearch -all -inline -not -exact $inputs_no_clk_no_reset $clk]
  }
  # Remove each reset from inputs list
  foreach rst $all_resets {
    set inputs_no_clk_no_reset [lsearch -all -inline -not -exact $inputs_no_clk_no_reset $rst]
  }
  # Remove each excluded signal from inputs list
  foreach exclude $signals_to_exclude {
    set inputs_no_clk_no_reset [lsearch -all -inline -not -exact $inputs_no_clk_no_reset $exclude]
  }
  # Generate toggle assumes
  set prim_clk [lindex $all_clocks 0]
  set prim_rst [lindex $all_resets 0]
  foreach input $inputs_no_clk_no_reset {
    assume -env "@(posedge $prim_clk) disable iff (!$prim_rst) \
      \$changed($input) \
        \|\-\> \
      s_eventually(\$changed($input))" -name "superlint__signal_toggle_assumes__${input}_ev_toggles"
    assume -env "@(posedge $prim_clk) disable iff (!$prim_rst) \
      \$rose($prim_rst) \
        \|\-\> \
      s_eventually(\$changed($input))" -name "superlint__signal_toggle_assumes__${input}_ev_changes_after_reset"
  }
}