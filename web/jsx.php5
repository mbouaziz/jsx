<?
  require_once('config.php5');

  function jsx($src, $lang, $env, $opt)
  {
    $descriptorspec = array(
      0 => array("pipe", "r"),
      1 => array("pipe", "w"),
      2 => array("pipe", "w")
    );
    
    $cmd_pre = '';
    $cmd_env = '';
    $cmd_post = '';
    foreach ($env as $filename => $type)
      if ($type == 'pre-js')
        $cmd_pre .= "-js $filename ";
      else if ($type == 'pre-ljs' || $type == 'pre-es5')
        $cmd_pre .= "-ljs $filename ";
      else if ($type == 'env')
        $cmd_env .= "-env $filename ";
      else if ($type == 'post-js')
        $cmd_post .= "-js $filename ";
      else if ($type == 'post-ljs' || $type == 'post-es5')
        $cmd_post .= "-ljs $filename ";

    $cmd_opt = '';
    foreach ($opt as $opt_name => $b)
      $cmd_opt .= ($b ? '-' : '-no-') . $opt_name . ' ';
    
    $cmd = jsx_bin . " $cmd_opt $cmd_pre -$lang STDIN $cmd_post $cmd_env";

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
