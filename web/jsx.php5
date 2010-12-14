<?
  require_once('config.php5');

  function jsx($src, $lang, $env, $opt)
  {
    $descriptorspec = array(
      0 => array("pipe", "r"),
      1 => array("pipe", "w"),
      2 => array("pipe", "w")
    );
    
    $cmd_env = '';
    foreach ($env as $filename => $b)
      if ($b)
        $cmd_env .= "-env $filename ";
        
    $cmd_opt = '';
    foreach ($opt as $opt_name => $b)
      $cmd_opt .= ($b ? '-' : '-no-') . $opt_name . ' ';
    
    $cmd = jsx_bin . " $cmd_opt -$lang STDIN $cmd_env";

    $process = proc_open($cmd, $descriptorspec, $pipes);
    
    if (!is_resource($process))
      return '<span class="err">Error when trying to run Jsx</span>';
      
    fwrite($pipes[0], $src);
    fclose($pipes[0]);
    
    $stdout = stream_get_contents($pipes[1]);
    $stderr = stream_get_contents($pipes[2]);
    fclose($pipes[1]);
    fclose($pipes[2]);
    
    $ret = proc_close($process);
    
    $res = '';
    
    /*
    if ($ret)
      $res .= '<span class="err">Return code ' . $ret . '</span>';
    */
      
    $res .= '<pre>' . $stdout . '<pre>';
    
    if ($stderr != '')
      $res .= '<hr /><pre>' . $stderr . '</pre>';
      
    return $res;
  }
?>
