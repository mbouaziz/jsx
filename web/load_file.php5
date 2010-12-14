<?
  require_once 'config.php5';
  
  $filename = $_REQUEST['filename'];
  
  if (strpos($filename, '..') !== false)
    die('');
  
  $filename = samples_dir . '/' . $filename;
  
  if (!is_file($filename))
    die('');
    
  readfile($filename);
?>
